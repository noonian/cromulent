(ns cromulent.pattern
  "Patterns and e-matching.

  A pattern is a term whose leaves may be pattern variables: symbols
  whose name starts with `?`. Variables never occur in terms, so a
  pattern is visibly a pattern:

    '[:* ?a 2]              matches any class holding a node [:* X two]
                            where `two` is the class of the leaf 2
    '[:+ ?x ?x]             a repeated variable must resolve to one class

  A match is {:class id :bindings {?a id ...}}; every id in it is a
  root. Matching is a backtracking search over the canonical nodes of
  each candidate class, and candidates come from the e-graph's
  operator index, so a pattern for `:*` never looks at a `:+` class.

  `instantiate` is the other direction: a pattern plus bindings
  becomes a class, adding whatever nodes are missing. It walks the
  pattern and calls `add-node` directly rather than building a term,
  because a term with class ids at its leaves would be read as a term
  with integer constants."
  (:require [cromulent.core :as eg]
            [cromulent.term :as term]))

(defn variable?
  "Is x a pattern variable (a symbol named ?something)?"
  [x]
  (and (symbol? x)
       (let [n (name x)]
         (and (< 1 (count n)) (= \? (nth n 0))))))

(defn variables
  "The set of pattern variables in p."
  [p]
  (cond
    (variable? p) #{p}
    (term/compound? p) (into #{} (mapcat variables) (term/children p))
    :else #{}))

(defn ground?
  "Does p contain no pattern variables?"
  [p]
  (empty? (variables p)))

(declare match-in)

(defn- match-children
  "Bindings extending binds under which the pattern children ps match
  the child classes ids, pairwise and in order."
  [g ps ids binds]
  (if (empty? ps)
    [binds]
    (into []
          (mapcat (fn [b] (match-children g (rest ps) (rest ids) b)))
          (match-in g (first ps) (eg/find g (first ids)) binds))))

(defn- match-in
  "Every bindings map extending binds under which pattern p matches
  the class with root id."
  [g p id binds]
  (cond
    (variable? p)
    (if-let [bound (get binds p)]
      (if (= bound id) [binds] [])
      [(assoc binds p id)])

    (term/compound? p)
    (let [op (term/operator p)
          n (term/arity p)]
      (into []
            (mapcat (fn [node]
                      (when (and (term/compound? node)
                                 (= op (term/operator node))
                                 (= n (term/arity node)))
                        (match-children g (term/children p) (term/children node) binds))))
            (:nodes (eg/eclass g id))))

    :else
    (if (contains? (:nodes (eg/eclass g id)) p) [binds] [])))

(defn match-class
  "Every bindings map under which pattern p matches the class of id.
  Empty when it does not match."
  [g p id]
  (match-in g p (eg/find g id) {}))

(defn ematch
  "Every match of pattern p in g, as a vector of
  {:class root-id :bindings {?var root-id ...}}."
  [g p]
  (cond
    (variable? p)
    (mapv (fn [r] {:class r :bindings {p r}}) (eg/roots g))

    (term/compound? p)
    (into []
          (mapcat (fn [id]
                    (let [id (eg/find g id)]
                      (map (fn [b] {:class id :bindings b}) (match-in g p id {})))))
          (get (:by-op g) (term/operator p)))

    :else
    (if-let [id (get (:memo g) p)]
      [{:class (eg/find g id) :bindings {}}]
      [])))

(defn instantiate
  "Add pattern p to g with each variable replaced by the class it is
  bound to. Returns [g' id]. Every variable in p must be bound."
  [g p bindings]
  (cond
    (variable? p)
    (if-let [id (get bindings p)]
      [g id]
      (throw (ex-info "unbound pattern variable" {:variable p :bindings bindings})))

    (term/compound? p)
    (let [[g ids] (reduce (fn [[g ids] child]
                            (let [[g id] (instantiate g child bindings)]
                              [g (conj ids id)]))
                          [g []]
                          (term/children p))]
      (eg/add-node g (term/make (term/operator p) ids)))

    :else
    (eg/add-node g p)))
