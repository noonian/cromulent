(ns cromulent.extract
  "Extraction: the cheapest term an e-class represents.

  A cost function is (fn [e-node child-costs] cost), given a
  canonical e-node and the best costs of its children in order; the
  default `ast-size` counts nodes. A cost is any value `compare`
  orders: a number, or a vector for a lexicographic cost (bendix's
  `no-D` counts derivative nodes before size). It must be monotone: a
  node must cost strictly more than any of its children, or a cycle
  such as x = x + 0 could be chosen and the term would never bottom
  out.

  `best-costs` is egg's Extractor: a bottom-up fixpoint over every
  class, costs in a vector indexed by class id, iterated until no
  class improves. A node whose child has no cost yet is skipped, which
  is why cycles are harmless. Ties are settled after it, by terms: of
  the nodes that head a cheapest term of a class, the class's is the
  one whose term is smallest under `cromulent.term/compare-nodes`,
  the term of each child being the one settled for the child's class.
  That order reads terms and never ids, so extraction is a function of
  what the e-graph says and not of which id names a class: the same on
  every runtime, and the same whichever root a union kept. `extract`
  (alias `yoink`) reads the term from the table."
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

(defn- cheapest
  "Vector, class id -> {:cost c :node n} for every root that has a
  term (nil elsewhere): the cost of the class's cheapest term under
  cost-fn, and some node that heads a term of that cost."
  [g cost-fn]
  (let [n (:next-id g)
        classes (:classes g)
        pass (fn [best]
               (reduce (fn [[best changed?] i]
                         (if-let [cls (nth classes i)]
                           (let [cur (nth best i)
                                 b (reduce-kv (fn [b _ node]
                                                (let [c (node-cost g best cost-fn node)]
                                                  (if (and c (or (nil? b) (neg? (compare (:cost c) (:cost b)))))
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

(defn- child-terms
  "The settled terms of node's children, in order, or nil when one of
  them is not settled."
  [g done node]
  (let [n (count node)]
    (loop [i 1, kids []]
      (if (< i n)
        (let [entry (nth done (eg/find g (nth node i)))]
          (when (map? entry)
            (recur (inc i) (conj kids (:term entry)))))
        kids))))

(defn- settle
  "done, a transient vector by class id, with the class of root r
  settled, and every class its cheapest terms reach. costs is the
  table `cheapest` made. A settled entry is {:cost c :node n :term t}:
  t the smallest, under `cromulent.term/compare-nodes`, of the terms
  the cheapest nodes of the class head, each child's term being its
  class's settled one, and n the node that heads it. A class is :open
  while its children are being settled; under a monotone cost no
  cheapest node reaches its own class, and a node that does is passed
  over."
  [g cost-fn costs done r]
  (if (or (some? (nth done r)) (nil? (nth costs r)))
    done
    (let [cost (:cost (nth costs r))
          nodes (:nodes (nth (:classes g) r))
          ;; the one node of a class is its cheapest: no cost to ask for
          one? (= 1 (count nodes))]
      (loop [nodes (seq (vals nodes))
             done (assoc! done r :open)
             pick nil]
        (if nodes
          (let [node (first nodes)]
            (if (or one?
                    (let [c (node-cost g costs cost-fn node)]
                      (and c (zero? (compare (:cost c) cost)))))
              (if (term/compound? node)
                (let [n (count node)
                      done (loop [i 1, done done]
                             (if (< i n)
                               (recur (inc i) (settle g cost-fn costs done (eg/find g (nth node i))))
                               done))
                      kids (child-terms g done node)
                      t (when kids (term/make (term/operator node) kids))]
                  (recur (next nodes) done
                         (if (and kids (or (nil? pick) (neg? (term/compare-nodes t (:term pick)))))
                           {:cost cost :node node :term t}
                           pick)))
                (recur (next nodes) done
                       (if (or (nil? pick) (neg? (term/compare-nodes node (:term pick))))
                         {:cost cost :node node :term node}
                         pick)))
              (recur (next nodes) done pick)))
          (assoc! done r pick))))))

(defn best-costs
  "Vector, class id -> {:cost c :node n :term t} for every root (nil
  elsewhere): the cheapest term of each class under cost-fn, its cost
  and the node that heads it. Of terms that cost the same, the
  smallest under `cromulent.term/compare-nodes` is the class's."
  [g cost-fn]
  (let [n (:next-id g)
        classes (:classes g)
        costs (cheapest g cost-fn)]
    (persistent!
     (reduce (fn [done r] (if (nth classes r) (settle g cost-fn costs done r) done))
             (transient (vec (repeat n nil)))
             (range n)))))

(defn extractor
  "A function of a class id returning {:cost c :term t}, sharing one
  cost table across calls."
  ([g] (extractor g ast-size))
  ([g cost-fn]
   (let [best (best-costs g cost-fn)]
     (fn [id]
       (let [r (eg/find g id)
             b (or (nth best r)
                   (throw (ex-info "class has no finite-cost term" {:class r})))]
         {:cost (:cost b) :term (:term b)})))))

(defn extract
  "The cheapest term in the class of id: {:cost c :term t}. Computes
  the cost table for the whole e-graph; use `extractor` to extract
  many classes from one table."
  ([g id] (extract g id ast-size))
  ([g id cost-fn] ((extractor g cost-fn) id)))

(def yoink "Alias of `extract`." extract)
