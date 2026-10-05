(ns cromulent.check
  "Invariant checker. `violations` returns a vector of maps, one per
  broken invariant of a rebuilt e-graph; empty means well-formed.
  Tests call it after every operation. It is not fast and need not be."
  (:require [cromulent.core :as eg]
            [cromulent.term :as term]))

(defn violations
  "Every broken invariant of g, as maps with a :type."
  [g]
  (let [{:keys [next-id uf classes by-op pending analysis-pending dirty? analyses ops op-names]} g
        memo (vec (eg/memo-entries g))
        memo-map (into {} memo)
        ids (range next-id)
        roots (filter #(eg/root? g %) ids)
        cls #(nth classes %)
        members (group-by #(nth uf %) ids)
        ;; node id -> stored node, over every class
        stored (into {} (for [r roots, entry (:nodes (cls r))] entry))]
    (-> []
        (into (when-not (= next-id (count uf) (count classes))
                [{:type :table-sizes :next-id next-id
                  :uf (count uf) :classes (count classes)}]))
        (into (for [id ids
                    :let [r? (eg/root? g id), c (cls id)]
                    :when (not= r? (some? c))]
                {:type :class-root-mismatch :id id :root? r? :class? (some? c)}))
        (into (for [r roots :when (not= r (:id (cls r)))]
                {:type :class-id-mismatch :id r :class-id (:id (cls r))}))
        (into (for [id ids
                    :let [r (nth uf id)]
                    :when (not= r (nth uf r))]
                {:type :union-find-not-flat :id id :points-at r}))
        (into (for [r roots
                    :let [actual (:members (cls r))]
                    :when (not= (get members r) (sort actual))]
                {:type :members :id r :expected (get members r) :actual actual}))
        (into (for [r roots :when (empty? (:nodes (cls r)))]
                {:type :empty-class :id r}))
        (into (for [[node _] memo
                    :when (not= node (eg/canonicalize g node))]
                {:type :stale-memo-key :node node}))
        (into (for [[node nid] memo
                    :when (not (and (contains? stored nid) (= node (get stored nid))))]
                {:type :memo-node-not-in-class :node node :id nid}))
        (into (for [r roots, [nid _] (:nodes (cls r))
                    :when (not= r (nth uf nid))]
                {:type :node-in-wrong-class :id r :node-id nid :its-class (nth uf nid)}))
        (into (for [r roots, [_ node] (:nodes (cls r))
                    :when (not= node (eg/canonicalize g node))]
                {:type :stale-class-node :id r :node node}))
        (into (for [r roots, [nid node] (:nodes (cls r))
                    :let [id (get memo-map node)]
                    :when (not= id nid)]
                {:type :class-node-not-in-memo :id r :node node :node-id nid :memo-id id}))
        (into (for [r roots, nid (:parents (cls r))
                    :let [p (get stored nid)]
                    :when (not (and (contains? stored nid)
                                    (term/compound? p)
                                    (some #(= % r) (term/children p))))]
                {:type :bad-parent :class r :parent p :parent-id nid}))
        (into (for [[nid node] stored
                    :when (term/compound? node)
                    child (term/children node)
                    :when (not (contains? (:parents (cls child)) nid))]
                {:type :missing-parent :node node :node-id nid :child child}))
        (into (let [expected (reduce (fn [idx r]
                                       (reduce (fn [idx node]
                                                 (if (term/compound? node)
                                                   (update idx (term/operator node) (fnil conj #{}) r)
                                                   idx))
                                               idx
                                               (vals (:nodes (cls r)))))
                                     {}
                                     roots)]
                (when (not= expected by-op)
                  [{:type :by-op-index :expected expected :actual by-op}])))
        (into (when-not (and (= (count ops) (count op-names))
                             (every? (fn [[op i]] (= op (nth op-names i nil))) ops))
                [{:type :operator-table :ops ops :op-names op-names}]))
        (into (when (or dirty? (seq pending) (seq analysis-pending))
                [{:type :pending-not-empty :dirty? dirty? :pending pending :analysis-pending analysis-pending}]))
        ;; data is closed under joining what the nodes say
        (into (for [{:keys [name make merge]} analyses
                    r roots
                    :let [c (cls r)
                          actual (get (:data c) name)
                          expected (reduce #(merge g %1 %2) actual (map #(make g % r) (vals (:nodes c))))]
                    :when (not= expected actual)]
                {:type :stale-analysis :analysis name :id r
                 :expected expected :actual actual})))))

(defn check!
  "g, or throws ex-info carrying the violations."
  [g]
  (let [vs (violations g)]
    (if (seq vs)
      (throw (ex-info "e-graph invariants violated" {:violations vs}))
      g)))
