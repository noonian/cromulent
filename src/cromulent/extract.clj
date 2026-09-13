(ns cromulent.extract
  "Extraction: the cheapest term an e-class represents.

  A cost function is (fn [e-node child-costs] number), given a
  canonical e-node and the best costs of its children in order; the
  default `ast-size` counts nodes. It must be monotone: a node must
  cost strictly more than any of its children, or a cycle such as
  x = x + 0 could be chosen and the term would never bottom out.

  `best-costs` is egg's Extractor: a bottom-up fixpoint over every
  class, costs in a vector indexed by class id, iterated until no
  class improves. A node whose child has no cost yet is skipped, which
  is why cycles are harmless. Ties go to the smaller node under
  `cromulent.term/compare-nodes`, so extraction is a function of the
  e-graph value alone, the same on every runtime. `extract` (alias
  `yoink`) builds the term top-down from each class's best node."
  (:require [cromulent.core :as eg]
            [cromulent.term :as term]))

(defn ast-size
  "The default cost: one per node."
  [_ child-costs]
  (reduce + 1 child-costs))

(defn- node-cost
  "{:cost c :node node} under cost-fn, or nil if a child has no cost yet."
  [g best cost-fn node]
  (if (term/compound? node)
    (let [cs (reduce (fn [cs c]
                       (if-let [b (nth best (eg/find g c))]
                         (conj cs (:cost b))
                         (reduced nil)))
                     []
                     (term/children node))]
      (when cs {:cost (cost-fn node cs) :node node}))
    {:cost (cost-fn node []) :node node}))

(defn best-costs
  "Vector, class id -> {:cost c :node n} for every root (nil elsewhere):
  the cheapest node of each class under cost-fn and the cost of the
  term it heads."
  [g cost-fn]
  (let [n (:next-id g)
        classes (:classes g)
        pass (fn [best]
               (reduce (fn [[best changed?] i]
                         (if-let [cls (nth classes i)]
                           (let [cur (nth best i)
                                 b (reduce (fn [b node]
                                             (let [c (node-cost g best cost-fn node)]
                                               (if (and c (or (nil? b)
                                                              (< (:cost c) (:cost b))
                                                              (and (= (:cost c) (:cost b))
                                                                   (neg? (term/compare-nodes node (:node b))))))
                                                 c
                                                 b)))
                                           cur
                                           (:nodes cls))]
                             (if (identical? b cur)
                               [best changed?]
                               [(assoc best i b) true]))
                           [best changed?]))
                       [best false]
                       (range n)))]
    (loop [best (vec (repeat n nil))]
      (let [[best changed?] (pass best)]
        (if changed? (recur best) best)))))

(defn- build [g best id]
  (let [r (eg/find g id)
        {:keys [node]} (or (nth best r)
                           (throw (ex-info "class has no finite-cost term" {:class r})))]
    (if (term/compound? node)
      (term/make (term/operator node) (mapv #(build g best %) (term/children node)))
      node)))

(defn extractor
  "A function of a class id returning {:cost c :term t}, sharing one
  cost table across calls."
  ([g] (extractor g ast-size))
  ([g cost-fn]
   (let [best (best-costs g cost-fn)]
     (fn [id]
       {:cost (:cost (nth best (eg/find g id)))
        :term (build g best id)}))))

(defn extract
  "The cheapest term in the class of id: {:cost c :term t}. Computes
  the cost table for the whole e-graph; use `extractor` to extract
  many classes from one table."
  ([g id] (extract g id ast-size))
  ([g id cost-fn] ((extractor g cost-fn) id)))

(def yoink "Alias of `extract`." extract)
