(ns cromulent.export-test
  "The egraph-serialize export: the naming of nodes and children, the
  costs, the roots and class data, and the printer's text, which must
  be the same on every runtime."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [cromulent.core :as eg]
            [cromulent.export :as export]
            [cromulent.extract :as ex]))

(defn- add-all [g ts]
  (reduce (fn [[g ids] t] (let [[g id] (eg/add g t)] [g (conj ids id)])) [g []] ts))

(deftest nodes-are-named-by-class-and-place-and-children-point-at-nodes
  (let [[g id] (eg/add (eg/egraph) [:* [:+ :x 1] [:+ :x 1]])
        d (export/serialize g {:cost ex/ast-size :roots [id]})
        nodes (get d "nodes")]
    (is (= ["0.0" "1.0" "2.0" "3.0"] (vec (keys nodes))) "one node per class, x, 1, the sum, the product")
    (is (= {"op" "*" "children" ["2.0" "2.0"] "eclass" "3" "cost" 7} (get nodes "3.0"))
        "the product points at the sum's node twice")
    (is (= {"op" "+" "children" ["0.0" "1.0"] "eclass" "2" "cost" 3} (get nodes "2.0")))
    (is (= {"op" "x" "children" [] "eclass" "0" "cost" 1} (get nodes "0.0")) "a leaf has no children and prints by name")
    (is (= {"op" "1" "children" [] "eclass" "1" "cost" 1} (get nodes "1.0")))
    (is (= ["3"] (get d "root_eclasses")))
    (is (= {} (get d "class_data")))
    (testing "every child names a node that exists, and the node's class is the child's"
      (doseq [[_ n] nodes, c (get n "children")]
        (is (contains? nodes c))
        (is (= (get-in nodes [c "eclass"]) (first (str/split c #"\."))))))))

(deftest a-merged-class-lists-its-nodes-in-order-and-a-parent-points-at-the-first
  (let [[g [m s q]] (add-all (eg/egraph) [[:* :a 2] [:<< :a 1] [:/ [:* :a 2] 2]])
        [g r] (eg/union g m s)
        g (eg/rebuild g)
        d (export/serialize g {:roots [q]})
        nodes (get d "nodes")
        in-r (filter (fn [[_ n]] (= (str r) (get n "eclass"))) nodes)]
    (is (= 2 (count in-r)) "the merged class holds the product and the shift")
    (is (= [(str r ".0") (str r ".1")] (mapv first in-r)))
    (is (= ["*" "<<"] (mapv #(get (second %) "op") in-r)) "in compare-nodes order: by arity, then operator")
    (is (= (str r ".0") (first (get-in nodes [(str (eg/find g q) ".0") "children"])))
        "the quotient's first child is the merged class's first node")
    (is (not (some #(contains? (second %) "cost") nodes)) "no cost function, no costs")
    (is (= [(str (eg/find g q))] (get d "root_eclasses")) "roots are canonicalized")))

(deftest class-data-and-costs-follow-the-options
  (let [[g id] (eg/add (eg/egraph) [:+ [:* 2 :x] :y])
        d (export/serialize g {:cost (fn [_ cs] [(count cs) (+ 1 (reduce + 0 (map second cs)))])
                               :roots [id id]
                               :class-data (fn [_ r] (cond (= r id) {:type "sum" "note" 7}
                                                           (= r 0) {}
                                                           :else nil))})]
    (is (not (some #(contains? % "cost") (vals (get d "nodes")))) "a vector cost is not a JSON number, so it is left out")
    (is (= ["4"] (get d "root_eclasses")) "a root named twice appears once")
    (is (= {"4" {"note" "7" "type" "sum"}} (get d "class_data")) "keys and values as strings, sorted; empty and nil skipped")
    (is (= {"op" "*" "children" ["0.0" "1.0"] "eclass" "2"} (get-in d ["nodes" "2.0"])))
    (is (= {"op" "times" "children" ["0.0" "1.0"] "eclass" "2" "cost" 3/2}
           (get-in (export/serialize g {:cost (fn [node _] (if (and (vector? node) (= :* (first node))) 3/2 1)) :op-str (fn [op] (if (= :* op) "times" (name op)))})
                   ["nodes" "2.0"]))
        "a ratio cost stays exact in the data, the printer makes it a double; op-str renames the operator")
    (is (= "X" (get-in (export/serialize g {:leaf-str (fn [x] (if (= :x x) "X" (str x)))}) ["nodes" "1.0" "op"])))))

(deftest the-printer
  (is (= "null" (export/->json nil)))
  (is (= "true" (export/->json true)))
  (is (= "\"a \\\"q\\\" b\\\\c\\n\"" (export/->json "a \"q\" b\\c\n")))
  (is (= "2·x" (subs (export/->json "2·x") 1 4)) "non-ASCII passes through")
  (is (= "0.5" (export/->json 1/2)))
  (is (= "-3" (export/->json -3)))
  (is (= "[]" (export/->json [])))
  (is (= "{}" (export/->json {})))
  (is (= "[1, \"a\", null, true]" (export/->json [1 "a" nil true])) "an array of scalars on one line")
  (is (= "{\n  \"a\": [\n    {\n      \"b\": 1\n    }\n  ],\n  \"k\": \"v\"\n}"
         (export/->json (sorted-map "k" "v" "a" [{"b" 1}])))
      "objects and arrays of objects indent by two")
  (is (= "{\n  \"k\": 1\n}" (export/->json {:k 1})) "a keyword key prints by name"))

(deftest the-json-text-of-a-script-graph
  (let [[g id] (eg/add (eg/egraph) [:+ [:* 2 :x] :y])]
    (is (= (str "{\n"
                "  \"nodes\": {\n"
                "    \"0.0\": {\n      \"op\": \"2\",\n      \"children\": [],\n      \"eclass\": \"0\",\n      \"cost\": 1\n    },\n"
                "    \"1.0\": {\n      \"op\": \"x\",\n      \"children\": [],\n      \"eclass\": \"1\",\n      \"cost\": 1\n    },\n"
                "    \"2.0\": {\n      \"op\": \"*\",\n      \"children\": [\"0.0\", \"1.0\"],\n      \"eclass\": \"2\",\n      \"cost\": 3\n    },\n"
                "    \"3.0\": {\n      \"op\": \"y\",\n      \"children\": [],\n      \"eclass\": \"3\",\n      \"cost\": 1\n    },\n"
                "    \"4.0\": {\n      \"op\": \"+\",\n      \"children\": [\"2.0\", \"3.0\"],\n      \"eclass\": \"4\",\n      \"cost\": 5\n    }\n"
                "  },\n"
                "  \"root_eclasses\": [\"4\"],\n"
                "  \"class_data\": {}\n"
                "}")
           (export/json g {:cost ex/ast-size :roots [id]})))))
