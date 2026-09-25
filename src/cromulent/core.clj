(ns cromulent.core
  "A persistent e-graph: the data structure of equality saturation, as
  a Clojure value. Every operation returns a new e-graph and leaves
  the old one intact.

  Design: egg (Willsey et al., POPL 2021) — deferred rebuilding and
  e-class analyses — with the persistent value as the primary
  representation. See IDEA.md.

  The e-graph is a map:

    :next-id   next e-class id; ids are dense integers
    :uf        vector, id -> parent id (union-find; a root points to itself)
    :size      vector, root id -> class size, for union by size
    :memo      the hashcons for compound nodes of arity two or less:
               packed key -> class id, the key being
               op-index·2^48 + a·2^24 + b for canonical children a and b
               (an absent child is 2^24 − 1), a fixnum on both runtimes;
               see `pack` and IDEA.md section 5
    :memo-other
               canonical e-node -> class id for leaves and for nodes of
               arity three or more (a leaf number would collide with a
               packed key)
    :ops       operator -> index, interned on first add
    :op-names  vector, index -> operator
    :classes   vector, root id -> class map, nil for non-roots
    :by-op     operator -> set of root ids whose class holds a node with
               that operator (the index e-matching starts from)
    :pending   vector of [parent-node class-id] entries whose parent
               node must be re-keyed in the hashcons (a worklist)
    :analysis-pending
               vector of class ids whose analysis data must be
               recomputed from their nodes (a worklist)
    :dirty?    true once a union has happened since the last rebuild
    :analyses  a vector of analysis maps (see `egraph`), possibly empty
    :analysis-state
               map, analysis name -> whatever that analysis keeps
               (an index, say); the core never touches it

  A class map is {:id :nodes :parents :data}: the e-nodes of the
  class, a map of parent e-node -> class id for every e-node that has
  this class as a child, and the analysis data, a map from analysis
  name to that analysis's data for the class.

  Between `union` and `rebuild` the hashcons, the parent maps and the
  class node sets may be stale; `rebuild` restores every invariant
  (see cromulent.check). That deferral is what makes saturation fast.
  `:by-op` is kept exact by `union` itself (it moves the smaller
  class's operators), so it only ever names roots."
  (:refer-clojure :exclude [find])
  (:require [cromulent.term :as term]))

(defn egraph
  "An empty e-graph. Options: :analyses, a vector of analyses (or
  :analysis, one), each

    {:name   k
     :make   (fn [eg e-node id] data)  ; the node's data; id is the class it is (or will be) in;
                                       ; children are canonical, read their data with `data`
     :merge  (fn [eg a b] data)        ; semilattice join of two data for one class:
                                       ; associative, commutative, idempotent; sees eg so it
                                       ; can canonicalize ids it stored
     :modify (fn [eg id] eg)           ; optional; may `add`, `union`, and keep state under
                                       ; [:analysis-state name]
     :reconcile (fn [eg id datas] eg)} ; optional; called with the data that met in class id:
                                       ; the two sides of a union, or the class's old data and
                                       ; every node's data at a recompute; may `add` and `union`

  A class's data under an analysis is closed under joining make over
  the class's canonical nodes: `union` joins provisionally and
  `rebuild` recomputes every class whose nodes or children changed,
  joining what the nodes now say into what the class had, so data
  that mentions class ids (as bendix's polynomials do) is refreshed
  when those ids stop being roots. The join's order must be
  well-founded (no infinite descending chains), which is what makes
  rebuild terminate; `rebuild` asserts it with a round limit and
  throws rather than spin if an analysis breaks it."
  ([] (egraph {}))
  ([{:keys [analysis analyses]}]
   {:next-id 0 :uf [] :size [] :memo {} :memo-other {} :ops {} :op-names []
    :classes [] :by-op {}
    :pending [] :analysis-pending [] :dirty? false
    :analyses (vec (concat (when analysis [analysis]) analyses))
    :analysis-state {}}))

(defn find-in
  "The canonical (root) id of the class containing id, read from the
  union-find vector uf itself. Hot loops fetch `(:uf eg)` once and call
  this; `find` is the same over the e-graph."
  [uf id]
  (loop [i id]
    (let [p (nth uf i)]
      (if (= p i) i (recur p)))))

(defn find
  "The canonical (root) id of the class containing id."
  [eg id]
  (find-in (:uf eg) id))

(defn root?
  "Is id the canonical id of its class?"
  [eg id]
  (= id (nth (:uf eg) id)))

(defn canonicalize
  "node with every child id replaced by its root. The very same node
  when no child changes."
  [eg node]
  (if (term/compound? node)
    (let [uf (:uf eg), n (count node)]
      (loop [i 1, node node]
        (if (< i n)
          (let [c (nth node i), r (find-in uf c)]
            (recur (inc i) (if (= c r) node (assoc node i r))))
          node)))
    node))

(defn eclass
  "The class map of the class containing id."
  [eg id]
  (nth (:classes eg) (find eg id)))

(defn nodes
  "The canonical e-nodes of the class containing id, as a set."
  [eg id]
  (into #{} (map #(canonicalize eg %)) (:nodes (eclass eg id))))

(defn roots
  "Every canonical class id."
  [eg]
  (filterv #(root? eg %) (range (:next-id eg))))

(defn class-count [eg] (count (roots eg)))

(defn data
  "The data of analysis name for the class containing id."
  [eg id name]
  (get (:data (eclass eg id)) name))

(defn node-count
  "Number of distinct e-nodes. Exact after `rebuild`."
  [eg]
  (+ (count (:memo eg)) (count (:memo-other eg))))

;; ---------------------------------------------------------------------------
;; the hashcons
;;
;; A compound node of arity two or less is keyed by one fixnum, packed by
;; multiplication and addition (shifts are slow on Jolt; IDEA.md section
;; 5): the operator's index times 2^48, plus the first child times 2^24,
;; plus the second child, an absent child written as 2^24 − 1. The sum
;; stays under 2^60, Chez's fixnum range. Leaves and wider nodes are
;; keyed by the node itself in :memo-other. Only a fresh node's lookup
;; pays for its key; stored nodes stay tagged vectors everywhere else.

(def ^:private op-scale 281474976710656)   ; 2^48
(def ^:private id-scale 16777216)          ; 2^24
(def ^:private absent 16777215)            ; 2^24 − 1
(def ^:private max-id 16777214)            ; ids stay below the sentinel
(def ^:private max-ops 4096)               ; 2^12 operators keep the key under 2^60

(defn- packable? [node]
  (and (term/compound? node) (<= (count node) 3)))

(defn- pack
  "The key of a canonical compound node of arity two or less."
  [op-index node]
  (let [n (count node)]
    (+ (* op-index op-scale)
       (* (if (> n 1) (nth node 1) absent) id-scale)
       (if (> n 2) (nth node 2) absent))))

(defn- unpack [op-names k]
  (let [op (nth op-names (quot k op-scale))
        a (rem (quot k id-scale) id-scale)
        b (rem k id-scale)]
    (cond (= a absent) [op]
          (= b absent) [op a]
          :else [op a b])))

(defn- memo-get
  "The class id stored for canonical node, or nil."
  [eg node]
  (if (packable? node)
    (when-let [i (get (:ops eg) (term/operator node))]
      (get (:memo eg) (pack i node)))
    (get (:memo-other eg) node)))

(defn- intern-op
  "[eg' index] for operator op, assigning an index on first sight."
  [eg op]
  (if-let [i (get (:ops eg) op)]
    [eg i]
    (let [i (count (:op-names eg))]
      (when (>= i max-ops)
        (throw (ex-info "too many operators for packed hashcons keys" {:limit max-ops :operator op})))
      [(-> eg (assoc-in [:ops op] i) (update :op-names conj op)) i])))

(defn- memo-put
  "eg with canonical node keyed to id."
  [eg node id]
  (if (packable? node)
    (let [[eg i] (intern-op eg (term/operator node))]
      (update eg :memo assoc (pack i node) id))
    (update eg :memo-other assoc node id)))

(defn memo-entries
  "Every [canonical-node class-id] pair of the hashcons, packed keys
  unpacked. For the checker and tests; not fast."
  [eg]
  (let [names (:op-names eg)]
    (concat (map (fn [[k id]] [(unpack names k) id]) (:memo eg))
            (seq (:memo-other eg)))))

(declare union)

(defn- run-modify [eg id]
  (reduce (fn [eg a] (if-let [modify (:modify a)] (modify eg id) eg))
          eg
          (:analyses eg)))

(defn- run-reconcile
  "Hand each analysis that reconciles the data maps that met in class id."
  [eg id datas]
  (reduce (fn [eg a]
            (if-let [reconcile (:reconcile a)]
              (reconcile eg id (map #(get % (:name a)) datas))
              eg))
          eg
          (:analyses eg)))

(defn- make-all
  "Data map for one node in class id."
  [eg node id]
  (reduce (fn [m a] (assoc m (:name a) ((:make a) eg node id))) {} (:analyses eg)))

(defn- merge-all
  "Join of two data maps."
  [eg da db]
  (reduce (fn [m a]
            (let [k (:name a)]
              (assoc m k ((:merge a) eg (get da k) (get db k)))))
          {}
          (:analyses eg)))

(defn- push-parents
  "worklist with every [parent-node class-id] entry of parents appended."
  [worklist parents]
  (reduce-kv (fn [w p pid] (conj w [p pid])) worklist parents))

(defn- push-parent-classes
  "worklist with the class id of every parent appended."
  [worklist parents]
  (reduce-kv (fn [w _ pid] (conj w pid)) worklist parents))

(defn add-node
  "Add one e-node whose children are class ids. Returns [eg' id]. The
  node is canonicalized first; an equal node already present returns
  its class instead of adding anything."
  [eg node]
  (let [node (canonicalize eg node)]
    (if-let [id (memo-get eg node)]
      [eg (find eg id)]
      (let [id (:next-id eg)
            _ (when (> id max-id)
                (throw (ex-info "too many e-classes for packed hashcons keys" {:limit max-id})))
            data (make-all eg node id)
            eg (-> eg
                   (assoc :next-id (inc id))
                   (update :uf conj id)
                   (update :size conj 1)
                   (memo-put node id)
                   (update :classes conj {:id id :nodes #{node} :parents {} :data data}))
            eg (if (term/compound? node)
                 (-> (reduce (fn [eg c] (update-in eg [:classes c :parents] assoc node id))
                             eg
                             (term/children node))
                     (update-in [:by-op (term/operator node)] (fnil conj #{}) id))
                 eg)]
        [(run-modify eg id) id]))))

(defn lookup
  "The canonical id of the class holding node (children are class
  ids), or nil when the e-graph has no such node. Adds nothing."
  [eg node]
  (when-let [id (memo-get eg (canonicalize eg node))]
    (find eg id)))

(defn add
  "Add a whole term, bottom-up, sharing every subterm already present.
  Returns [eg' id]."
  [eg t]
  (if (term/compound? t)
    (let [[eg ids] (reduce (fn [[eg ids] child]
                             (let [[eg id] (add eg child)]
                               [eg (conj ids id)]))
                           [eg []]
                           (term/children t))]
      (add-node eg (term/make (term/operator t) ids)))
    (add-node eg t)))

(defn- merge-into
  "Merge the smaller of two maps or sets into the larger."
  [a b]
  (if (< (count a) (count b)) (into b a) (into a b)))

(defn union
  "Assert that the classes of a and b are equal. Returns [eg' root].
  Deferred: the smaller class's parents are queued for `rebuild`,
  which re-keys them in the hashcons and finds the congruences that
  follow; nothing else is repaired now."
  [eg a b]
  (let [ra (find eg a), rb (find eg b)]
    (if (= ra rb)
      [eg ra]
      (let [size (:size eg)
            [ra rb] (if (< (nth size ra) (nth size rb)) [rb ra] [ra rb])
            classes (:classes eg)
            ca (nth classes ra), cb (nth classes rb)
            analyses? (seq (:analyses eg))
            by-op (reduce (fn [idx node]
                            (if (term/compound? node)
                              (update idx (term/operator node) #(conj (disj (or % #{}) rb) ra))
                              idx))
                          (:by-op eg)
                          (:nodes cb))
            eg (-> eg
                   (assoc :by-op by-op)
                   (assoc-in [:uf rb] ra)
                   (assoc-in [:size ra] (+ (nth size ra) (nth size rb)))
                   (assoc-in [:classes rb] nil)
                   (assoc :dirty? true)
                   (update :pending push-parents (:parents cb)))
            ;; the join is provisional: rebuild recomputes the merged class
            ;; from its nodes, and every parent whose child's data changed
            data (when analyses? (merge-all eg (:data ca) (:data cb)))
            eg (assoc-in eg [:classes ra] {:id ra
                                           :nodes (merge-into (:nodes ca) (:nodes cb))
                                           :parents (merge-into (:parents ca) (:parents cb))
                                           :data data})
            eg (if analyses?
                 (-> (cond-> (update eg :analysis-pending conj ra)
                       (not= data (:data ca)) (update :analysis-pending push-parent-classes (:parents ca))
                       (not= data (:data cb)) (update :analysis-pending push-parent-classes (:parents cb)))
                     (run-reconcile ra [(:data ca) (:data cb)]))
                 eg)]
        [(run-modify eg ra) ra]))))

(defn- process-pending
  "Drain the congruence worklist: re-key each queued parent node under
  its canonical form, unioning it with any class already holding that
  form. Unions queue more work; the loop ends when the worklist is
  empty. Stale hashcons keys are left behind for
  `compress-and-canonicalize`, which rebuilds the hashcons anyway; a
  canonical lookup can never hit a stale key because a non-root id
  never becomes a root again."
  [eg]
  (loop [eg eg]
    (let [pending (:pending eg)]
      (if (empty? pending)
        eg
        (let [[p pid] (peek pending)
              eg (assoc eg :pending (pop pending))
              p' (canonicalize eg p)
              root (find eg pid)
              other (memo-get eg p')
              [eg root] (if (and (some? other) (not= (find eg other) root))
                          (union eg other root)
                          [eg root])]
          (recur (memo-put eg p' root)))))))

(defn- recompute
  "Join what the class of c's canonical nodes now say into its data.
  Hand the old data and every node's data to the analyses that
  reconcile. When the join changed the data: store it, queue the
  class's parents, run modify."
  [eg c]
  (let [r (find eg c)
        cls (nth (:classes eg) r)
        old (:data cls)
        datas (mapv #(make-all eg (canonicalize eg %) r) (:nodes cls))
        new (reduce #(merge-all eg %1 %2) old datas)
        changed? (not= old new)
        eg (if changed?
             (-> eg
                 (assoc-in [:classes r :data] new)
                 (update :analysis-pending push-parent-classes (:parents cls)))
             eg)
        eg (run-reconcile eg r (cons old datas))]
    (if changed? (run-modify eg r) eg)))

(defn- process-analysis-pending
  "Drain the analysis worklist in rounds: recompute every queued class
  once per round; the classes their changes affect form the next
  round. A round that changes nothing ends the loop. Every round
  strictly descends some class's data in its analysis's order, so a
  well-founded order guarantees the loop ends; the round limit turns
  an analysis that breaks that into an exception instead of a hang."
  [eg]
  (let [limit (+ 1000 (* 16 (:next-id eg)))]
    (loop [eg eg, rounds 0]
      (let [todo (into #{} (map #(find eg %)) (:analysis-pending eg))]
        (cond
          (empty? todo) eg
          (> rounds limit) (throw (ex-info "analysis did not converge: its join is not well-founded"
                                           {:rounds rounds :classes todo
                                            :data (into {} (map (fn [c] [c (:data (nth (:classes eg) c))])) todo)}))
          :else (recur (reduce recompute (assoc eg :analysis-pending []) todo) (inc rounds)))))))

(defn- compress-and-canonicalize
  "Once the worklists are empty: point every id straight at its root,
  rewrite every class's nodes and parents in canonical form, and
  rebuild the hashcons from the classes. Linear in the size of the
  e-graph; the first thing to amortize when a benchmark says so."
  [eg]
  (let [n (:next-id eg)
        uf (reduce (fn [uf i]
                     (let [r (find eg i)]
                       (if (= r (nth uf i)) uf (assoc uf i r))))
                   (:uf eg)
                   (range n))
        eg (assoc eg :uf uf)
        classes (reduce (fn [classes i]
                          (if-let [cls (nth classes i)]
                            (assoc classes i
                                   (assoc cls
                                          :nodes (into #{} (map #(canonicalize eg %)) (:nodes cls))
                                          :parents (into {}
                                                         (map (fn [[p pid]] [(canonicalize eg p) (find eg pid)]))
                                                         (:parents cls))))
                            classes))
                        (:classes eg)
                        (range n))
        eg (assoc eg :classes classes :memo {} :memo-other {})]
    (reduce (fn [eg i]
              (if-let [cls (nth classes i)]
                (reduce (fn [eg node] (memo-put eg node i)) eg (:nodes cls))
                eg))
            eg
            (range n))))

(defn rebuild
  "Restore congruence closure and every invariant after unions.
  Idempotent; a no-op when no union has happened since the last one."
  [eg]
  (if-not (:dirty? eg)
    eg
    (let [eg (loop [eg eg]
               (if (and (empty? (:pending eg)) (empty? (:analysis-pending eg)))
                 eg
                 (recur (-> eg process-pending process-analysis-pending))))]
      (assoc (compress-and-canonicalize eg) :dirty? false))))
