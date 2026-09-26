(ns cromulent.export
  "The e-graph in the egraph-serialize JSON format, the format the
  egraphs-good tools share (github.com/egraphs-good/egraph-serialize):
  egg and egglog write it, the egraph-visualizer and the extraction
  gym read it. `serialize` gives the data with string keys as the
  format spells them, `json` prints it, and `->json` is the printer,
  a small one of its own so the same text comes out on the JVM, on
  Jolt and in ClojureScript.

    {\"nodes\": {\"4.0\": {\"op\": \"+\", \"children\": [\"2.0\", \"3.0\"], \"eclass\": \"4\", \"cost\": 5}, …},
     \"root_eclasses\": [\"4\"],
     \"class_data\": {\"4\": {\"type\": \"polynomial\", \"poly\": \"2·x + y\"}}}

  A node is named by its class and its place among the class's nodes
  in `cromulent.term/compare-nodes` order, 4.0, 4.1, as egg names
  them. The format points at nodes, not classes, so a child is the
  first node of the child class, 2.0, and a reader takes that node's
  class. Along a saturation the ids follow hash iteration order,
  which differs per runtime, so two runtimes may name the same graph
  differently; the counts and the shape agree, and a script's ids are
  the same everywhere."
  (:require [clojure.string :as str]
            [cromulent.core :as eg]
            [cromulent.extract :as ex]
            [cromulent.term :as term]))

;; ---------------------------------------------------------------------------
;; the printer

(defn- escape [s]
  (str "\""
       (-> s
           (str/replace "\\" "\\\\")
           (str/replace "\"" "\\\"")
           (str/replace "\n" "\\n")
           (str/replace "\r" "\\r")
           (str/replace "\t" "\\t"))
       "\""))

(defn- key-str [k] (if (keyword? k) (name k) (str k)))

(defn- number-str
  "An integer as itself, anything else (a ratio on the JVM) as a
  double, so no runtime prints 1/2."
  [x]
  (if (integer? x) (str x) (str (double x))))

(defn- scalar? [x]
  (or (nil? x) (boolean? x) (string? x) (keyword? x) (number? x)))

(defn ->json
  "x as JSON text, indented two spaces, an object's entries in the
  order its map gives them (a sorted map prints in order), an array
  of scalars on one line."
  ([x] (->json x ""))
  ([x indent]
   (cond
     (nil? x) "null"
     (true? x) "true"
     (false? x) "false"
     (string? x) (escape x)
     (keyword? x) (escape (name x))
     (number? x) (number-str x)
     (map? x)
     (if (empty? x)
       "{}"
       (let [in (str indent "  ")]
         (str "{\n"
              (str/join ",\n" (for [[k v] x] (str in (escape (key-str k)) ": " (->json v in))))
              "\n" indent "}")))
     (or (sequential? x) (set? x))
     (cond
       (empty? x) "[]"
       (every? scalar? x) (str "[" (str/join ", " (map #(->json % indent) x)) "]")
       :else (let [in (str indent "  ")]
               (str "[\n" (str/join ",\n" (map #(str in (->json % in)) x)) "\n" indent "]")))
     :else (escape (str x)))))

;; ---------------------------------------------------------------------------
;; the data

(def ^:private top-order {"nodes" 0 "root_eclasses" 1 "class_data" 2})
(def ^:private node-order {"op" 0 "children" 1 "eclass" 2 "cost" 3 "subsumed" 4})

(defn- ordered
  "A sorted map whose keys print in the order rank gives them."
  [rank kvs]
  (into (sorted-map-by (fn [a b] (compare (rank a) (rank b)))) kvs))

(defn- node-cost
  "The cost of the cheapest term node heads, from the best-cost
  table of its children; nil while a child has no finite term."
  [g best cost-fn node]
  (if (term/compound? node)
    (let [cs (reduce (fn [cs c]
                       (if-let [b (nth best (eg/find g c))]
                         (conj cs (:cost b))
                         (reduced nil)))
                     []
                     (term/children node))]
      (when cs (cost-fn node cs)))
    (cost-fn node [])))

(defn- default-str [x] (if (keyword? x) (name x) (str x)))

(defn serialize
  "g as egraph-serialize data, string keys, ready for `->json`. Options:

    :cost       a cost function, (fn [node child-costs] cost) as
                cromulent.extract takes; each node gets the cost of the
                cheapest term it heads when that is a number (a ratio
                prints as a double); a vector cost, or a node whose child
                has no finite term, gets none and the format's default of
                1 stands
    :roots      class ids for root_eclasses, canonicalized
    :class-data (fn [g root] map), the class_data of each root: string
                keys and values as the format has them, \"type\" being
                the one the egraph-visualizer colours by; nil or empty
                for none
    :op-str     how an operator prints, default `name`
    :leaf-str   how a leaf prints, default `name` for a keyword and
                `str` otherwise"
  [g {:keys [cost roots class-data op-str leaf-str]
      :or {op-str default-str leaf-str default-str}}]
  (let [classes (eg/roots g)
        by-class (into {} (map (fn [r] [r (vec (sort term/compare-nodes (eg/nodes g r)))])) classes)
        node-id (fn [c i] (str c "." i))
        best (when cost (ex/best-costs g cost))
        rank (into {} (for [r classes, i (range (count (by-class r)))] [(node-id r i) [r i]]))
        class-rank (into {} (map (fn [r] [(str r) r])) classes)
        nodes (ordered rank
                       (for [r classes, [i node] (map-indexed vector (by-class r))]
                         (let [c (when best (node-cost g best cost node))]
                           [(node-id r i)
                            (ordered node-order
                                    (cond-> {"op" (if (term/compound? node) (op-str (term/operator node)) (leaf-str node))
                                             "children" (if (term/compound? node)
                                                          (mapv #(node-id (eg/find g %) 0) (term/children node))
                                                          [])
                                             "eclass" (str r)}
                                      (number? c) (assoc "cost" c)))])))
        data (ordered class-rank
                      (when class-data
                        (keep (fn [r]
                                (let [m (class-data g r)]
                                  (when (seq m)
                                    [(str r) (into (sorted-map) (map (fn [[k v]] [(key-str k) (str v)])) m)])))
                              classes)))]
    (ordered top-order
             {"nodes" nodes
              "root_eclasses" (vec (distinct (map #(str (eg/find g %)) roots)))
              "class_data" data})))

(defn json
  "g as egraph-serialize JSON text; opts as `serialize` takes them."
  ([g] (json g {}))
  ([g opts] (->json (serialize g opts))))
