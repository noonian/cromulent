(ns cromulent.check
  "Invariant checker. `violations` returns a vector of maps, one per
  broken invariant of a rebuilt e-graph; empty means well-formed.
  Tests call it after every operation. It is not fast and need not be."
  (:require [cromulent.core :as eg]
            [cromulent.term :as term]))

(defn violations
  "Every broken invariant of g, as maps with a :type."
  [g]
  (let [{:keys [next-id uf size classes by-op pending analysis-pending dirty? analyses ops op-names]} g
        memo (vec (eg/memo-entries g))
        memo-map (into {} memo)
        ids (range next-id)
        roots (filter #(eg/root? g %) ids)
        cls #(nth classes %)]
    (-> []
        (into (when-not (= next-id (count uf) (count size) (count classes))
                [{:type :table-sizes :next-id next-id
                  :uf (count uf) :size (count size) :classes (count classes)}]))
        (into (for [id ids
                    :let [r? (eg/root? g id), c (cls id)]
                    :when (not= r? (some? c))]
                {:type :class-root-mismatch :id id :root? r? :class? (some? c)}))
        (into (for [r roots :when (not= r (:id (cls r)))]
                {:type :class-id-mismatch :id r :class-id (:id (cls r))}))
        (into (for [[node _] memo
                    :when (not= node (eg/canonicalize g node))]
                {:type :stale-memo-key :node node}))
        (into (for [[node id] memo
                    :let [r (eg/find g id)]
                    :when (not (contains? (:nodes (cls r)) node))]
                {:type :memo-node-not-in-class :node node :id id}))
        (into (for [r roots, node (:nodes (cls r))
                    :when (not= node (eg/canonicalize g node))]
                {:type :stale-class-node :id r :node node}))
        (into (for [r roots, node (:nodes (cls r))
                    :let [id (get memo-map node)]
                    :when (or (nil? id) (not= (eg/find g id) r))]
                {:type :class-node-not-in-memo :id r :node node :memo-id id}))
        (into (for [r roots, [p pid] (:parents (cls r))
                    :when (or (not= p (eg/canonicalize g p))
                              (not (eg/root? g pid))
                              (not (some #(= % r) (term/children p)))
                              (not (contains? (:nodes (cls pid)) p)))]
                {:type :bad-parent :class r :parent p :parent-class pid}))
        (into (for [[node _] memo
                    :when (term/compound? node)
                    child (term/children node)
                    :when (not (contains? (:parents (cls child)) node))]
                {:type :missing-parent :node node :child child}))
        (into (let [expected (reduce (fn [idx r]
                                       (reduce (fn [idx node]
                                                 (if (term/compound? node)
                                                   (update idx (term/operator node) (fnil conj #{}) r)
                                                   idx))
                                               idx
                                               (:nodes (cls r))))
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
                          expected (reduce #(merge g %1 %2) actual (map #(make g % r) (:nodes c)))]
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
