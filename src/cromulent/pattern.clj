(ns cromulent.pattern
  "Patterns and e-matching.

  A pattern is a term whose leaves may be pattern variables: symbols
  whose name starts with `?`. Variables never occur in terms, so a
  pattern is visibly a pattern:

    '[:* ?a 2]              matches any class holding a node [:* X two]
                            where `two` is the class of the leaf 2
    '[:+ ?x ?x]             a repeated variable must resolve to one class

  A match is {:class id :bindings {?a id ...}}; every id in it is a
  root. Candidates come from the e-graph's operator index, so a
  pattern for `:*` never looks at a `:+` class.

  A pattern is compiled once (`compile`) into a plan of nested vectors,
  `[:var register symbol]`, `[:node op arity child-plans]` and
  `[:leaf value]`, and matched by index loops: variables are registers (egg's term
  for its e-matching machine; nothing to do with slotted e-graphs)
  in one long-array per search, −1 for unbound, written on bind and
  restored on backtrack; a repeated variable compares ids with `=`;
  child ids are taken as they are when the graph is clean (after
  `rebuild` every stored node is canonical) and passed through the
  union-find otherwise; each match reaches a callback holding the
  registers, and `ematch` copies them into the bindings map. `ematch`,
  `match-class` and `instantiate` accept a pattern or its compiled
  form. IDEA.md sections 5 and 6 record the measurements behind this.

  `instantiate` is the other direction: a pattern plus bindings
  becomes a class, adding whatever nodes are missing. It walks the
  plan and calls `add-node` directly rather than building a term,
  because a term with class ids at its leaves would be read as a term
  with integer constants."
  (:refer-clojure :exclude [compile])
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

;; ---------------------------------------------------------------------------
;; compiling

(defn compiled?
  "Is p the compiled form of a pattern?"
  [p]
  (and (map? p) (true? (::compiled p))))

(defn compile
  "The compiled form of pattern p: {:plan plan :vars [symbol ...]
  :pattern p}, variables given register numbers in order of first
  occurrence. A
  compiled pattern compiles to itself."
  [p]
  (if (compiled? p)
    p
    (let [regs (atom {})
          plan (letfn [(c [p]
                         (cond
                           (variable? p)
                           (let [i (or (get @regs p)
                                       (let [i (count @regs)] (swap! regs assoc p i) i))]
                             [:var i p])

                           (term/compound? p)
                           [:node (term/operator p) (term/arity p) (mapv c (term/children p))]

                           :else [:leaf p]))]
                 (c p))
          vars (reduce (fn [v [sym i]] (assoc v i sym))
                       (vec (repeat (count @regs) nil))
                       @regs)]
      {::compiled true :plan plan :vars vars :pattern p})))

;; ---------------------------------------------------------------------------
;; matching

(defn- match-plan
  "Call k once for every way plan matches the class whose root is id,
  with the registers holding the bindings at that moment. uf is the union-find
  vector; clean? says stored child ids are roots already."
  [g uf clean? plan id ^longs regs k]
  (case (nth plan 0)
    :var
    (let [s (nth plan 1), b (aget regs s)]
      (cond
        (= b -1) (do (aset regs s (long id)) (k) (aset regs s -1))
        (= b id) (k)
        :else nil))

    :leaf
    (when (contains? (:nodes (nth (:classes g) id)) (nth plan 1))
      (k))

    :node
    (let [op (nth plan 1), n (nth plan 2), plans (nth plan 3)]
      (reduce (fn [_ node]
                (when (and (term/compound? node)
                           (= op (term/operator node))
                           (= n (term/arity node)))
                  (letfn [(go [j]
                            (if (< j n)
                              (let [c (term/child node j)
                                    c (if clean? c (eg/find-in uf c))]
                                (match-plan g uf clean? (nth plans j) c regs #(go (inc j))))
                              (k)))]
                    (go 0)))
                nil)
              nil
              (:nodes (nth (:classes g) id))))))

(defn- bindings-of
  "The bindings map for vars from the registers."
  [vars ^longs regs]
  (let [n (count vars)]
    (loop [i 0, m {}]
      (if (< i n)
        (recur (inc i) (assoc m (nth vars i) (aget regs i)))
        m))))

(defn ematch
  "Every match of pattern p in g, as a vector of
  {:class root-id :bindings {?var root-id ...}}."
  [g p]
  (let [{:keys [plan vars pattern]} (compile p)]
    (case (nth plan 0)
      :var (mapv (fn [r] {:class r :bindings {pattern r}}) (eg/roots g))
      :leaf (if-let [id (eg/lookup g pattern)]
              [{:class id :bindings {}}]
              [])
      :node (let [op (nth plan 1)
                  uf (:uf g)
                  clean? (not (:dirty? g))
                  regs (long-array (count vars) -1)
                  out (transient [])]
              (reduce (fn [_ id]
                        (let [r (eg/find-in uf id)]
                          (match-plan g uf clean? plan r regs
                                      (fn [] (conj! out {:class r :bindings (bindings-of vars regs)})))
                          nil))
                      nil
                      (get (:by-op g) op))
              (persistent! out)))))

(defn match-class
  "Every bindings map under which pattern p matches the class of id.
  Empty when it does not match."
  [g p id]
  (let [{:keys [plan vars pattern]} (compile p)
        r (eg/find g id)]
    (case (nth plan 0)
      :var [{pattern r}]
      :leaf (if (contains? (:nodes (eg/eclass g r)) pattern) [{}] [])
      :node (let [regs (long-array (count vars) -1)
                  out (transient [])]
              (match-plan g (:uf g) (not (:dirty? g)) plan r regs
                          (fn [] (conj! out (bindings-of vars regs))))
              (persistent! out)))))

;; ---------------------------------------------------------------------------
;; instantiating

(defn- instantiate-plan [g plan bindings]
  (case (nth plan 0)
    :var
    (let [v (nth plan 2)]
      (if-let [id (get bindings v)]
        [g id]
        (throw (ex-info "unbound pattern variable" {:variable v :bindings bindings}))))

    :leaf
    (eg/add-node g (nth plan 1))

    :node
    (let [op (nth plan 1), n (nth plan 2), plans (nth plan 3)]
      (loop [j 0, g g, ids []]
        (if (< j n)
          (let [[g id] (instantiate-plan g (nth plans j) bindings)]
            (recur (inc j) g (conj ids id)))
          (eg/add-node g (term/make op ids)))))))

(defn instantiate
  "Add pattern p to g with each variable replaced by the class it is
  bound to. Returns [g' id]. Every variable in p must be bound."
  [g p bindings]
  (instantiate-plan g (:plan (compile p)) bindings))
