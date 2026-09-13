(ns cromulent.check
  "Invariant checker. `violations` returns a vector of maps, one per
  broken invariant of a rebuilt e-graph; empty means well-formed.
  Tests call it after every operation. It is not fast and need not be."
  (:require [cromulent.core :as eg]
            [cromulent.term :as term]))

(defn violations
  "Every broken invariant of g, as maps with a :type."
  [g]
  (let [{:keys [next-id uf size memo classes pending analysis]} g
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
                    :let [id (get memo node)]
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
        (into (when (seq pending)
                [{:type :pending-not-empty :pending pending}]))
        (into (when analysis
                (let [{:keys [make merge]} analysis]
                  (for [r roots
                        :let [c (cls r)
                              expected (reduce merge (map #(make g %) (:nodes c)))]
                        :when (not= expected (:data c))]
                    {:type :stale-analysis :id r :expected expected :actual (:data c)})))))))

(defn check!
  "g, or throws ex-info carrying the violations."
  [g]
  (let [vs (violations g)]
    (if (seq vs)
      (throw (ex-info "e-graph invariants violated" {:violations vs}))
      g)))
