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
  `[:leaf value]`, and matched by index loops: variables are registers
  (egg's term for its e-matching machine; nothing to do with slotted
  e-graphs) in one long-array per search, −1 for unbound, written on
  bind and restored on backtrack; a repeated variable compares ids
  with `=`; child ids are taken as they are when the graph is clean
  (after `rebuild` every stored node is canonical) and passed through
  the union-find otherwise; each match reaches a callback holding the
  registers. `ematch` copies them into a bindings map per match;
  `ematch-flat` writes them into one flat long-array, class root then
  registers, which is what the runner reads (IDEA.md section 5, second
  pass). `ematch`, `match-class` and `instantiate` accept a pattern or
  its compiled form.

  The compiled form also holds a program for the other direction: a
  post-order list of instructions, `[:leaf value dest]` and
  `[:node op operand-registers dest]`, over one register file holding
  the variables first and temporaries after. `instantiate-registers`
  runs it with the variables' classes loaded, looking each node of
  arity two or less up by its packed hashcons key and calling
  `add-node` only when the node is new, so a hit allocates nothing.
  `instantiate` loads the registers from a bindings map and runs the
  same program. A right-hand side is compiled against the registers
  of its left-hand side (`compile` with fixed variables), so the
  runner hands one match's registers to both."
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
  "The compiled form of pattern p:

    {:plan plan          the matcher's plan, see the namespace doc
     :vars [symbol ...]  register number -> variable
     :program [...]      instantiation instructions, post-order
     :result register    where the program leaves the instantiated class
     :nregs n            registers the program needs: variables, then temporaries
     :pattern p}

  Variables take register numbers in order of first occurrence. With
  `fixed`, a vector of variables, those keep their positions in it
  and any others follow: a right-hand side compiled with its
  left-hand side's `:vars` reads the same registers. A compiled
  pattern compiles to itself; with `fixed` it is recompiled from its
  pattern."
  ([p] (compile p nil))
  ([p fixed]
   (if (and (compiled? p) (nil? fixed))
     p
     (let [p (if (compiled? p) (:pattern p) p)
           regs (atom (zipmap fixed (range)))
           vars (atom (vec fixed))
           plan (letfn [(c [p]
                          (cond
                            (variable? p)
                            (let [i (or (get @regs p)
                                        (let [i (count @regs)]
                                          (swap! regs assoc p i)
                                          (swap! vars conj p)
                                          i))]
                              [:var i p])

                            (term/compound? p)
                            [:node (term/operator p) (term/arity p) (mapv c (term/children p))]

                            :else [:leaf p]))]
                  (c p))
           next-reg (atom (count @vars))
           program (atom [])
           result (letfn [(emit [pl]
                            (case (nth pl 0)
                              :var (nth pl 1)
                              :leaf (let [d @next-reg]
                                      (swap! next-reg inc)
                                      (swap! program conj [:leaf (nth pl 1) d])
                                      d)
                              :node (let [operands (mapv emit (nth pl 3))
                                          d @next-reg]
                                      (swap! next-reg inc)
                                      (swap! program conj [:node (nth pl 1) operands d])
                                      d)))]
                    (emit plan))]
       {::compiled true :plan plan :vars @vars :pattern p
        :program @program :result result :nregs @next-reg}))))

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

(defn- grow
  "buf copied into a long-array twice its size."
  [^longs buf]
  (let [n (count buf), out (long-array (* 2 n))]
    (loop [i 0]
      (when (< i n)
        (aset out i (aget buf i))
        (recur (inc i))))
    out))

(defn ematch-flat
  "Every match of pattern p in g written into a flat long-array: per
  match the class root, then one register per variable of p in
  `:vars` order, so a match's stride is one more than the variable
  count. buf is the array to fill, reused across searches and
  replaced by one twice as large whenever it fills. Returns
  [buf' n-matches]; the caller keeps buf' for the next search."
  [g p ^longs buf]
  (let [{:keys [plan vars pattern]} (compile p)
        k (count vars)
        stride (inc k)
        cell (atom buf)
        n (long-array 2 0)                       ; [fill capacity]
        _ (aset n 1 (long (count buf)))
        put! (fn [r ^longs regs]
               (let [i (aget n 0)
                     ^longs b (if (<= (+ i stride) (aget n 1))
                                @cell
                                (let [b (grow @cell)]
                                  (aset n 1 (* 2 (aget n 1)))
                                  (reset! cell b)))]
                 (aset b i (long r))
                 (loop [j 0]
                   (when (< j k)
                     (aset b (+ i 1 j) (aget regs j))
                     (recur (inc j))))
                 (aset n 0 (+ i stride))))]
    (case (nth plan 0)
      :var (let [regs (long-array 1)]
             (reduce (fn [_ r] (aset regs 0 (long r)) (put! r regs) nil) nil (eg/roots g)))
      :leaf (when-let [id (eg/lookup g pattern)]
              (put! id (long-array 0)))
      :node (let [op (nth plan 1)
                  uf (:uf g)
                  clean? (not (:dirty? g))
                  regs (long-array k -1)]
              (reduce (fn [_ id]
                        (let [r (eg/find-in uf id)]
                          (match-plan g uf clean? plan r regs (fn [] (put! r regs)))
                          nil))
                      nil
                      (get (:by-op g) op))))
    [@cell (quot (aget n 0) stride)]))

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

(defn instantiate-registers
  "Run compiled pattern c's program on g with its variables' classes
  already in regs (register i holds variable i of `:vars`; regs has
  `:nregs` slots). Returns g', and leaves the instantiated class in
  register `:result`. Each compound node of arity two or less is
  looked up by its packed key first and built only when absent."
  [g c ^longs regs]
  (let [program (:program c), n (count program)]
    (loop [i 0, g g, uf (:uf g), memo (:memo g), ops (:ops g)]
      (if (< i n)
        (let [ins (nth program i)]
          (case (nth ins 0)
            :leaf
            (let [[g id] (eg/add-node g (nth ins 1))]
              (aset regs (nth ins 2) (long id))
              (recur (inc i) g (:uf g) (:memo g) (:ops g)))

            :node
            (let [op (nth ins 1), operands (nth ins 2), dest (nth ins 3), arity (count operands)]
              (if (<= arity 2)
                (let [a (when (> arity 0) (eg/find-in uf (aget regs (nth operands 0))))
                      b (when (> arity 1) (eg/find-in uf (aget regs (nth operands 1))))
                      key (eg/packed-key ops op a b)
                      id (when key (get memo key))]
                  (if id
                    (do (aset regs dest (long (eg/find-in uf id)))
                        (recur (inc i) g uf memo ops))
                    (let [[g id] (eg/add-node g (case arity 0 [op] 1 [op a] [op a b]))]
                      (aset regs dest (long id))
                      (recur (inc i) g (:uf g) (:memo g) (:ops g)))))
                (let [ids (loop [j 0, ids (transient [])]
                            (if (< j arity)
                              (recur (inc j) (conj! ids (eg/find-in uf (aget regs (nth operands j)))))
                              (persistent! ids)))
                      [g id] (eg/add-node g (term/make op ids))]
                  (aset regs dest (long id))
                  (recur (inc i) g (:uf g) (:memo g) (:ops g)))))))
        g))))

(defn instantiate
  "Add pattern p to g with each variable replaced by the class it is
  bound to. Returns [g' id]. Every variable in p must be bound."
  [g p bindings]
  (let [c (compile p)
        vars (:vars c)
        k (count vars)
        regs (long-array (:nregs c) -1)]
    (loop [i 0]
      (when (< i k)
        (let [v (nth vars i)
              id (get bindings v)]
          (when (nil? id)
            (throw (ex-info "unbound pattern variable" {:variable v :bindings bindings})))
          (aset regs i (long id))
          (recur (inc i)))))
    (let [g (instantiate-registers g c regs)]
      [g (aget regs (:result c))])))
