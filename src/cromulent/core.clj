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
    :memo      canonical e-node -> class id (the hashcons)
    :classes   vector, root id -> class map, nil for non-roots
    :by-op     operator -> set of root ids whose class holds a node with
               that operator (the index e-matching starts from)
    :pending   vector of [parent-node class-id] entries whose parent
               node must be re-keyed in the hashcons (a worklist)
    :analysis-pending
               vector of [parent-node class-id] entries whose class's
               analysis data must be refreshed (a worklist)
    :dirty?    true once a union has happened since the last rebuild
    :analysis  an analysis map or nil (see `egraph`)

  A class map is {:id :nodes :parents :data}: the e-nodes of the
  class, a map of parent e-node -> class id for every e-node that has
  this class as a child, and the analysis data.

  Between `union` and `rebuild` the hashcons, the parent maps and the
  class node sets may be stale; `rebuild` restores every invariant
  (see cromulent.check). That deferral is what makes saturation fast.
  `:by-op` is kept exact by `union` itself (it moves the smaller
  class's operators), so it only ever names roots."
  (:refer-clojure :exclude [find])
  (:require [cromulent.term :as term]))

(defn egraph
  "An empty e-graph. Options:

    :analysis  {:name   k
                :make   (fn [eg e-node] data)  ; children are canonical; read their data with `eclass`
                :merge  (fn [a b] data)        ; lattice join: associative, commutative, idempotent
                :modify (fn [eg id] eg)}       ; optional; may `add` and `union`"
  ([] (egraph {}))
  ([{:keys [analysis]}]
   {:next-id 0 :uf [] :size [] :memo {} :classes [] :by-op {}
    :pending [] :analysis-pending [] :dirty? false :analysis analysis}))

(defn find
  "The canonical (root) id of the class containing id."
  [eg id]
  (let [uf (:uf eg)]
    (loop [i id]
      (let [p (nth uf i)]
        (if (= p i) i (recur p))))))

(defn root?
  "Is id the canonical id of its class?"
  [eg id]
  (= id (nth (:uf eg) id)))

(defn canonicalize
  "node with every child id replaced by its root."
  [eg node]
  (term/map-children #(find eg %) node))

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

(defn node-count
  "Number of distinct e-nodes. Exact after `rebuild`."
  [eg]
  (count (:memo eg)))

(declare union)

(defn- run-modify [eg id]
  (if-let [modify (get-in eg [:analysis :modify])]
    (modify eg id)
    eg))

(defn- push-parents
  "worklist with every [parent-node class-id] entry of parents appended."
  [worklist parents]
  (reduce-kv (fn [w p pid] (conj w [p pid])) worklist parents))

(defn add-node
  "Add one e-node whose children are class ids. Returns [eg' id]. The
  node is canonicalized first; an equal node already present returns
  its class instead of adding anything."
  [eg node]
  (let [node (canonicalize eg node)]
    (if-let [id (get (:memo eg) node)]
      [eg (find eg id)]
      (let [id (:next-id eg)
            data (when-let [make (get-in eg [:analysis :make])] (make eg node))
            eg (-> eg
                   (assoc :next-id (inc id))
                   (update :uf conj id)
                   (update :size conj 1)
                   (update :memo assoc node id)
                   (update :classes conj {:id id :nodes #{node} :parents {} :data data}))
            eg (if (term/compound? node)
                 (-> (reduce (fn [eg c] (update-in eg [:classes c :parents] assoc node id))
                             eg
                             (term/children node))
                     (update-in [:by-op (term/operator node)] (fnil conj #{}) id))
                 eg)]
        [(run-modify eg id) id]))))

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
            analysis (:analysis eg)
            data (when analysis ((:merge analysis) (:data ca) (:data cb)))
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
                   (assoc-in [:classes ra] {:id ra
                                            :nodes (merge-into (:nodes ca) (:nodes cb))
                                            :parents (merge-into (:parents ca) (:parents cb))
                                            :data data})
                   (assoc-in [:classes rb] nil)
                   (assoc :dirty? true)
                   (update :pending push-parents (:parents cb)))
            eg (if analysis
                 (cond-> eg
                   (not= data (:data ca)) (update :analysis-pending push-parents (:parents ca))
                   (not= data (:data cb)) (update :analysis-pending push-parents (:parents cb)))
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
              other (get (:memo eg) p')
              [eg root] (if (and (some? other) (not= (find eg other) root))
                          (union eg other root)
                          [eg root])]
          (recur (update eg :memo assoc p' root)))))))

(defn- process-analysis-pending
  "Drain the analysis worklist: re-make each queued parent node and
  join the result into its class's data; when that changes the data,
  queue the class's parents and run modify."
  [eg]
  (let [{:keys [make merge]} (:analysis eg)]
    (loop [eg eg]
      (let [pending (:analysis-pending eg)]
        (if (empty? pending)
          eg
          (let [[p pid] (peek pending)
                eg (assoc eg :analysis-pending (pop pending))
                root (find eg pid)
                cls (nth (:classes eg) root)
                old (:data cls)
                new (merge old (make eg (canonicalize eg p)))]
            (recur (if (= old new)
                     eg
                     (-> eg
                         (assoc-in [:classes root :data] new)
                         (update :analysis-pending push-parents (:parents cls))
                         (run-modify root))))))))))

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
        memo (reduce (fn [memo i]
                       (if-let [cls (nth classes i)]
                         (reduce (fn [memo node] (assoc memo node i)) memo (:nodes cls))
                         memo))
                     {}
                     (range n))]
    (assoc eg :classes classes :memo memo)))

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
