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
    :pending   set of root ids whose parents need repair
    :analysis  an analysis map or nil (see `egraph`)

  A class map is {:id :nodes :parents :data}: the e-nodes of the
  class, a map of parent e-node -> class id for every e-node that has
  this class as a child, and the analysis data.

  Between `union` and `rebuild` the hashcons, the parent maps and the
  class node sets may be stale; `rebuild` restores every invariant
  (see cromulent.check). That deferral is what makes saturation fast."
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
   {:next-id 0 :uf [] :size [] :memo {} :classes [] :pending #{} :analysis analysis}))

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
                 (reduce (fn [eg c] (update-in eg [:classes c :parents] assoc node id))
                         eg
                         (term/children node))
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

(defn union
  "Assert that the classes of a and b are equal. Returns [eg' root].
  Deferred: the hashcons and parent maps are repaired by `rebuild`."
  [eg a b]
  (let [ra (find eg a), rb (find eg b)]
    (if (= ra rb)
      [eg ra]
      (let [size (:size eg)
            [ra rb] (if (< (nth size ra) (nth size rb)) [rb ra] [ra rb])
            classes (:classes eg)
            ca (nth classes ra), cb (nth classes rb)
            join (get-in eg [:analysis :merge])
            eg (-> eg
                   (assoc-in [:uf rb] ra)
                   (assoc-in [:size ra] (+ (nth size ra) (nth size rb)))
                   (assoc-in [:classes ra] {:id ra
                                            :nodes (into (:nodes ca) (:nodes cb))
                                            :parents (into (:parents ca) (:parents cb))
                                            :data (when join (join (:data ca) (:data cb)))})
                   (assoc-in [:classes rb] nil)
                   (update :pending conj ra))]
        [(run-modify eg ra) ra]))))

(defn- repair
  "Re-key the parents of class c in the hashcons under their canonical
  form, unioning any two classes whose parents now coincide (a new
  congruence), then refresh the analysis data of those parent classes."
  [eg c]
  (let [c (find eg c)
        parents (:parents (nth (:classes eg) c))
        eg (reduce-kv
             (fn [eg p pid]
               (let [eg (update eg :memo dissoc p)
                     p' (canonicalize eg p)
                     root (find eg pid)
                     other (get (:memo eg) p')
                     [eg root] (if (and (some? other) (not= (find eg other) root))
                                 (union eg other root)
                                 [eg root])]
                 (update eg :memo assoc p' root)))
             eg
             parents)]
    (if-let [{:keys [make merge]} (:analysis eg)]
      (reduce-kv
        (fn [eg p pid]
          (let [root (find eg pid)
                old (:data (nth (:classes eg) root))
                new (merge old (make eg (canonicalize eg p)))]
            (if (= old new)
              eg
              (-> eg
                  (assoc-in [:classes root :data] new)
                  (update :pending conj root)
                  (run-modify root)))))
        eg
        parents)
      eg)))

(defn- compress-and-canonicalize
  "Once the worklist is empty: point every id straight at its root,
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
  Idempotent; a no-op when nothing is pending."
  [eg]
  (if (empty? (:pending eg))
    eg
    (let [eg (loop [eg eg]
               (if (empty? (:pending eg))
                 eg
                 (let [todo (into #{} (map #(find eg %)) (:pending eg))]
                   (recur (reduce repair (assoc eg :pending #{}) todo)))))]
      (compress-and-canonicalize eg))))
