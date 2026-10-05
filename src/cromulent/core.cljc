(ns cromulent.core
  "A persistent e-graph: the data structure of equality saturation, as
  a Clojure value. Every operation returns a new e-graph and leaves
  the old one intact.

  Design: egg (Willsey et al., POPL 2021) — deferred rebuilding and
  e-class analyses — with the persistent value as the primary
  representation. See IDEA.md.

  The e-graph is a map:

    :next-id   next id; ids are dense integers. `add-node` allocates
               one per new e-node, and that id names the node for good:
               it is the node's key in its class, in its children's
               parents and in the hashcons, whatever the node's
               canonical form becomes. Through the union-find the same
               id names the class the node is in
    :uf        vector, id -> root id (union-find; a root points to
               itself). Always flat: every id points straight at its
               root, so `find` is one read
    :memo      the hashcons for compound nodes of arity two or less:
               packed key -> node id, the key being
               op-index·2^42 + a·2^21 + b for canonical children a and b
               (an absent child is 2^21 − 1), under 2^53: a fixnum on the
               JVM and on Chez, and exact in a JavaScript double; see
               `pack` and IDEA.md section 5
    :memo-other
               canonical e-node -> node id for leaves and for nodes of
               arity three or more (a leaf number would collide with a
               packed key)
    :ops       operator -> index, interned on first add
    :op-names  vector, index -> operator
    :classes   vector, root id -> class map, nil for non-roots
    :by-op     operator -> set of root ids whose class holds a node with
               that operator (the index e-matching starts from)
    :pending   vector of node ids whose node must be re-keyed in the
               hashcons and rewritten in its class (a worklist)
    :analysis-pending
               vector of ids whose class's analysis data must be
               recomputed from its nodes (a worklist)
    :dirty?    true once a union has happened since the last rebuild
    :analyses  a vector of analysis maps (see `egraph`), possibly empty
    :analysis-state
               map, analysis name -> whatever that analysis keeps
               (an index, say); the core never touches it

  A class map is {:id :members :nodes :parents :data}: every id that
  names the class, as a vector; the e-nodes of the class, a map of
  node id -> e-node; the ids of the e-nodes that have this class as a
  child, as a set; and the analysis data, a map from analysis name to
  that analysis's data for the class. A node that turns out congruent
  to another is retired: its id stays a member and leaves :nodes.

  Between `union` and `rebuild` the hashcons keys and the stored nodes
  of the queued parents may be stale; `rebuild` restores every
  invariant (see cromulent.check). That deferral is what makes
  saturation fast. `:uf` and `:by-op` are kept exact by `union` itself
  (it repoints the merged class's ids and moves its operators).

  Every operation writes only what it changes and shares the rest with
  the e-graph it was given: `rebuild` touches the classes of the
  queued parents and nothing else, so its cost follows the unions and
  not the size of the e-graph."
  (:refer-clojure :exclude [find parents])
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
   {:next-id 0 :uf [] :memo {} :memo-other {} :ops {} :op-names []
    :classes [] :by-op {}
    :pending [] :analysis-pending [] :dirty? false
    :analyses (vec (concat (when analysis [analysis]) analyses))
    :analysis-state {}}))

(defn find-in
  "The canonical (root) id of the class containing id, read from the
  union-find vector uf itself. Hot loops fetch `(:uf eg)` once and call
  this; `find` is the same over the e-graph. One read: `union` keeps
  every id pointing straight at its root."
  [uf id]
  (nth uf id))

(defn find
  "The canonical (root) id of the class containing id."
  [eg id]
  (nth (:uf eg) id))

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
          (let [c (nth node i), r (nth uf c)]
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
  (into #{} (map #(canonicalize eg %)) (vals (:nodes (eclass eg id)))))

(defn parents
  "The e-nodes that have the class containing id as a child, as a
  vector of [canonical-node root-id] pairs, root-id the class the node
  is in. Before `rebuild` two entries may read the same node: they are
  congruent and not yet merged."
  [eg id]
  (let [uf (:uf eg), classes (:classes eg)]
    (mapv (fn [nid]
            (let [r (nth uf nid)]
              [(canonicalize eg (get (:nodes (nth classes r)) nid)) r]))
          (:parents (eclass eg id)))))

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
;; 5): the operator's index times 2^42, plus the first child times 2^21,
;; plus the second child, an absent child written as 2^21 − 1. The sum
;; stays under 2^53: a fixnum on Chez and the JVM, and exact in a
;; JavaScript double, so the same layout serves all three runtimes; the
;; largest key is 2^53 − 1 exactly. Leaves and wider nodes are keyed by
;; the node itself in :memo-other. Only a fresh node's lookup pays for
;; its key; stored nodes stay tagged vectors everywhere else.

(def ^:private op-scale 4398046511104)     ; 2^42
(def ^:private id-scale 2097152)           ; 2^21
(def ^:private absent 2097151)             ; 2^21 − 1
(def ^:private max-id 2097150)             ; ids stay below the sentinel
(def ^:private max-ops 2048)               ; 2^11 operators keep the key under 2^53

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

(defn packed-key
  "The hashcons key of the canonical node [op a b], a and b class ids
  with b, or both, nil for arity one or zero; nil when op has no index
  yet, in which case the node is new. ops is (:ops eg), read once by a
  caller looking many nodes up; the lookup is (get (:memo eg) key)."
  [ops op a b]
  (when-let [i (get ops op)]
    (+ (* i op-scale)
       (* (if (nil? a) absent a) id-scale)
       (if (nil? b) absent b))))

(defn- memo-get
  "The node id stored for canonical node, or nil."
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

(defn- memo-remove
  "eg without the key of node, a node `memo-put` stored."
  [eg node]
  (if (packable? node)
    (update eg :memo dissoc (pack (get (:ops eg) (term/operator node)) node))
    (update eg :memo-other dissoc node)))

(defn memo-entries
  "Every [node node-id] pair of the hashcons, packed keys unpacked.
  For the checker and tests; not fast."
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
  "worklist with every node id of parents appended. Either worklist
  takes them: a node's id names its class too."
  [worklist parents]
  (reduce conj worklist parents))

(defn- weight
  "What merging cls away costs: an id to repoint per member, a node
  to re-key per parent."
  [cls]
  (+ (count (:members cls)) (count (:parents cls))))

(defn add-node
  "Add one e-node whose children are class ids. Returns [eg' id], id
  the canonical id of its class. The node is canonicalized first; an
  equal node already present returns its class instead of adding
  anything."
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
                   (memo-put node id)
                   (update :classes conj {:id id :members [id] :nodes {id node} :parents #{} :data data}))
            eg (if (term/compound? node)
                 (-> (reduce (fn [eg c] (update-in eg [:classes c :parents] conj id))
                             eg
                             (term/children node))
                     (update-in [:by-op (term/operator node)] (fnil conj #{}) id))
                 eg)]
        ;; a modify may union the new class into another
        (let [eg (run-modify eg id)]
          [eg (find eg id)])))))

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
  "Merge the smaller of two maps, sets or vectors into the larger."
  [a b]
  (if (< (count a) (count b)) (into b a) (into a b)))

(defn union
  "Assert that the classes of a and b are equal. Returns [eg' root].
  The class that is cheaper to move is merged into the other: the one
  with fewer members and parents, the younger root on a tie. Its ids
  are pointed at the surviving root now, which keeps the union-find
  flat. Deferred: its parents are queued for `rebuild`, which re-keys
  them in the hashcons and finds the congruences that follow; nothing
  else is repaired now."
  [eg a b]
  (let [ra (find eg a), rb (find eg b)]
    (if (= ra rb)
      [eg ra]
      (let [classes (:classes eg)
            wa (weight (nth classes ra)), wb (weight (nth classes rb))
            [ra rb] (if (or (< wa wb) (and (= wa wb) (< rb ra))) [rb ra] [ra rb])
            ca (nth classes ra), cb (nth classes rb)
            analyses? (seq (:analyses eg))
            by-op (reduce-kv (fn [idx _ node]
                               (if (term/compound? node)
                                 (update idx (term/operator node) #(conj (disj (or % #{}) rb) ra))
                                 idx))
                             (:by-op eg)
                             (:nodes cb))
            uf (reduce (fn [uf id] (assoc uf id ra)) (:uf eg) (:members cb))
            eg (-> eg
                   (assoc :by-op by-op)
                   (assoc :uf uf)
                   (assoc-in [:classes rb] nil)
                   (assoc :dirty? true)
                   (update :pending push-parents (:parents cb)))
            ;; the join is provisional: rebuild recomputes the merged class
            ;; from its nodes, and every parent whose child's data changed
            data (when analyses? (merge-all eg (:data ca) (:data cb)))
            eg (assoc-in eg [:classes ra] {:id ra
                                           :members (merge-into (:members ca) (:members cb))
                                           :nodes (merge-into (:nodes ca) (:nodes cb))
                                           :parents (merge-into (:parents ca) (:parents cb))
                                           :data data})
            eg (if analyses?
                 (-> (cond-> (update eg :analysis-pending conj ra)
                       (not= data (:data ca)) (update :analysis-pending push-parents (:parents ca))
                       (not= data (:data cb)) (update :analysis-pending push-parents (:parents cb)))
                     (run-reconcile ra [(:data ca) (:data cb)]))
                 eg)]
        ;; a modify may union ra into another class
        (let [eg (run-modify eg ra)]
          [eg (find eg ra)])))))

(defn- retire
  "eg with the node of id nid retired in favour of the node of id
  other, which has the same canonical form: their classes are unioned,
  and nid leaves its class's nodes and its children's parents. nid
  stays a member of the class."
  [eg nid other]
  (let [[eg _] (union eg other nid)
        r (find eg nid)
        node (get (:nodes (nth (:classes eg) r)) nid)]
    (reduce (fn [eg c] (update-in eg [:classes (find eg c) :parents] disj nid))
            (update-in eg [:classes r :nodes] dissoc nid)
            (term/children node))))

(defn- process-pending
  "Drain the congruence worklist. Each queued id names a node one of
  whose children was merged away: the node is re-keyed in the hashcons
  under its canonical form and rewritten in its class, and when
  another node already has that form the two are congruent, so the
  queued one is retired into it. Unions queue more work; the loop ends
  when the worklist is empty, and then every stored node is canonical
  and the hashcons holds exactly the stored nodes. Only the classes of
  queued nodes are written. A canonical lookup can never hit a key
  that is still stale, because a non-root id never becomes a root
  again."
  [eg]
  (loop [eg eg]
    (let [pending (:pending eg)]
      (if (empty? pending)
        eg
        (let [nid (peek pending)
              eg (assoc eg :pending (pop pending))
              r (find eg nid)
              node (get (:nodes (nth (:classes eg) r)) nid)
              node' (when node (canonicalize eg node))]
          (if (identical? node node')
            ;; retired since it was queued, or repaired by an earlier entry
            (recur eg)
            (let [eg (memo-remove eg node)
                  other (memo-get eg node')]
              (recur (if (nil? other)
                       (-> eg
                           (memo-put node' nid)
                           (assoc-in [:classes r :nodes nid] node'))
                       (retire eg nid other))))))))))

(defn- recompute
  "Join what the class of c's canonical nodes now say into its data.
  Hand the old data and every node's data to the analyses that
  reconcile. When the join changed the data: store it, queue the
  class's parents, run modify."
  [eg c]
  (let [r (find eg c)
        cls (nth (:classes eg) r)
        old (:data cls)
        datas (mapv #(make-all eg (canonicalize eg %) r) (vals (:nodes cls)))
        new (reduce #(merge-all eg %1 %2) old datas)
        changed? (not= old new)
        eg (if changed?
             (-> eg
                 (assoc-in [:classes r :data] new)
                 (update :analysis-pending push-parents (:parents cls)))
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

(defn rebuild
  "Restore congruence closure and every invariant after unions.
  Idempotent; a no-op when no union has happened since the last one.
  It writes what the unions touched and shares the rest with eg."
  [eg]
  (if-not (:dirty? eg)
    eg
    (loop [eg eg]
      (if (and (empty? (:pending eg)) (empty? (:analysis-pending eg)))
        (assoc eg :dirty? false)
        (recur (-> eg process-pending process-analysis-pending))))))
