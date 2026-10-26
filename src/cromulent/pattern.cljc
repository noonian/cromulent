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

  `ematch-flat` can be asked for only the fresh matches, those with a
  node stamped after an epoch, and still says how many matches there
  are. A pattern of one operator over variables and leaves, which most
  rules are, is matched by one pass over that operator's nodes with no
  call per child (`match-one-node`).

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
  with the registers holding the bindings at that moment. uf is the
  union-find vector; clean? says stored child ids are roots already.

  k takes one argument, fresh?: whether the match has a node stamped
  after the epoch `since`, or fresh? was true coming in. stamps is the
  e-graph's stamp vector. A match that is not fresh was a match of the
  same class under the same bindings when that epoch ended: none of
  its nodes has been added, moved or re-keyed since, and two nodes
  that were not beside each other become so only when one of them
  moves or the other is re-keyed. A caller that wants every match
  passes fresh? true, and no stamp is read."
  [g uf clean? stamps since plan id ^longs regs fresh? k]
  (case (nth plan 0)
    :var
    (let [s (nth plan 1), b (aget regs s)]
      (cond
        (= b -1) (do (aset regs s (long id)) (k fresh?) (aset regs s -1))
        (= b id) (k fresh?)
        :else nil))

    :leaf
    (let [nid (eg/node-id g (nth plan 1))]
      (when (and (some? nid) (= id (eg/find-in uf nid)))
        (k (or fresh? (> (nth stamps nid) since)))))

    :node
    (let [op (nth plan 1), n (nth plan 2), plans (nth plan 3)
          cls (nth (:classes g) id)
          ;; a class not stamped since holds no node stamped since
          look? (and (not fresh?) (> (:stamp cls) since))]
      (reduce-kv (fn [_ nid node]
                   (when (and (term/compound? node)
                              (= op (term/operator node))
                              (= n (term/arity node)))
                     (letfn [(go [j fresh?]
                               (if (< j n)
                                 (let [c (term/child node j)
                                       c (if clean? c (eg/find-in uf c))]
                                   (match-plan g uf clean? stamps since (nth plans j) c regs fresh?
                                               #(go (inc j) %)))
                                 (k fresh?)))]
                       (go 0 (or fresh? (and look? (> (nth stamps nid) since))))))
                   nil)
                 nil
                 (:nodes cls)))))

(defn- match-one-node
  "Every match of a pattern of one operator over variables and leaves,
  whose plan is `plan`: each node of that operator is looked at once,
  with no call per child. write is called with the class root for
  every fresh match, the registers holding its bindings; with all?
  every match is fresh. Returns how many matches there are. A stale
  match costs the comparisons that show it is a match and nothing
  more. The order is `match-plan`'s."
  [g uf clean? stamps since all? plan ^longs regs write]
  (let [op (nth plan 1), n (nth plan 2), plans (nth plan 3)
        classes (:classes g)
        leaf-at (long-array n -1)                ; the class a leaf child must be, -1 for a variable
        reg-at (long-array n -1)                 ; a variable child's register
        again (long-array n 0)                   ; 1 when an earlier child is the same variable
        ;; nil when a leaf is not in g; else whether a leaf is fresh, and so every match
        leaves (loop [j 0, fresh? false]
                 (if (< j n)
                   (let [p (nth plans j)]
                     (if (= :var (nth p 0))
                       (let [s (nth p 1)]
                         (aset reg-at j (long s))
                         (loop [i 0]
                           (when (< i j)
                             (if (= s (aget reg-at i))
                               (aset again j 1)
                               (recur (inc i)))))
                         (recur (inc j) fresh?))
                       (when-let [lid (eg/node-id g (nth p 1))]
                         (aset leaf-at j (long (eg/find-in uf lid)))
                         (recur (inc j) (or fresh? (> (nth stamps lid) since))))))
                   fresh?))
        found (long-array 1 0)]
    (when (some? leaves)
      (let [all? (or all? leaves)]
        (reduce
         (fn [_ id]
           (let [r (eg/find-in uf id)
                 cls (nth classes r)
                 look? (and (not all?) (> (:stamp cls) since))]
             (reduce-kv
              (fn [_ nid node]
                (when (and (term/compound? node)
                           (= op (term/operator node))
                           (= n (term/arity node))
                           (loop [j 0]
                             (if (< j n)
                               (let [c (term/child node j)
                                     c (if clean? c (eg/find-in uf c))
                                     l (aget leaf-at j)]
                                 (cond
                                   (>= l 0) (when (= c l) (recur (inc j)))
                                   (zero? (aget again j)) (do (aset regs (aget reg-at j) (long c))
                                                              (recur (inc j)))
                                   :else (when (= c (aget regs (aget reg-at j))) (recur (inc j)))))
                               true)))
                  (aset found 0 (inc (aget found 0)))
                  (when (or all? (and look? (> (nth stamps nid) since)))
                    (write r regs)))
                nil)
              nil
              (:nodes cls))))
         nil
         (get (:by-op g) op))))
    (aget found 0)))

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
                          (match-plan g uf clean? nil 0 plan r regs true
                                      (fn [_] (conj! out {:class r :bindings (bindings-of vars regs)})))
                          nil))
                      nil
                      (get (:by-op g) op))
              (persistent! out)))))

(defn- grow
  "buf copied into a long-array twice its size."
  [^longs buf]
  (let [n (count buf), out (long-array (max 1 (* 2 n)))]
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
  replaced by one twice as large whenever it fills.

  With since, an epoch, only the fresh matches are written: those
  with a node stamped after it. A match with none was a match of the
  same class under the same bindings when that epoch ended, so a
  caller that acted on every match then has nothing to learn from it.
  Every match is counted either way. A pattern that is one variable
  or one leaf is not filtered.

  A pattern of one operator is matched by one pass over that
  operator's nodes (`match-one-node`); a deeper one by the walk of
  `match-plan`, every match counted and the fresh ones written. What
  is written, and in what order, is the same either way, and is the
  order of `ematch`.

  Returns [buf' n-written n-found]; the caller keeps buf' for the
  next search."
  ([g p buf] (ematch-flat g p buf nil))
  ([g p ^longs buf since]
   (let [{:keys [plan vars pattern]} (compile p)
         k (count vars)
         stride (inc k)
         cell (atom buf)
         n (long-array 3 0)                      ; [fill capacity found]
         _ (aset n 1 (long (count buf)))
         put! (fn [r ^longs regs]
                (let [i (aget n 0)
                      ^longs b (if (<= (+ i stride) (aget n 1))
                                 @cell
                                 (loop [b (grow @cell)]
                                   (if (<= (+ i stride) (count b))
                                     (do (aset n 1 (long (count b)))
                                         (reset! cell b))
                                     (recur (grow b)))))]
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
                   regs (long-array k -1)
                   stamps (:stamps g)
                   all? (nil? since)
                   since (if all? 0 since)]
               (if (not-any? #(= :node (nth % 0)) (nth plan 3))
                 (aset n 2 (long (match-one-node g uf clean? stamps since all? plan regs put!)))
                 (reduce (fn [_ id]
                           (let [r (eg/find-in uf id)]
                             (match-plan g uf clean? stamps since plan r regs all?
                                         (fn [fresh?]
                                           (aset n 2 (inc (aget n 2)))
                                           (when fresh? (put! r regs))))
                             nil))
                         nil
                         (get (:by-op g) op)))))
     (let [written (quot (aget n 0) stride)]
       [@cell written (if (= :node (nth plan 0)) (aget n 2) written)]))))

(defn match-class
  "Every bindings map under which pattern p matches the class of id.
  Empty when it does not match."
  [g p id]
  (let [{:keys [plan vars pattern]} (compile p)
        r (eg/find g id)]
    (case (nth plan 0)
      :var [{pattern r}]
      :leaf (if (= r (eg/lookup g pattern)) [{}] [])
      :node (let [regs (long-array (count vars) -1)
                  out (transient [])]
              (match-plan g (:uf g) (not (:dirty? g)) nil 0 plan r regs true
                          (fn [_] (conj! out (bindings-of vars regs))))
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

;; ---------------------------------------------------------------------------
;; witnesses

(defn witness-id
  "The id a witness w of pattern p stands for: the root node's id for a
  compound, w itself for a variable or a leaf."
  [p w]
  (if (term/compound? p) (nth w 0) w))

(defn witness
  "Where pattern p occurs in g under bindings, node by node: a variable
  as the id it is bound to, a leaf as its node's id, and a compound as
  [node-id w1 ... wk], the id of a node of g whose canonical form is
  the compound over its children's classes, then the children's
  witnesses. nil when some node of the instance is not in g. Adds
  nothing. A journal (cromulent.core, :explain?) records the witnesses
  of both sides of a rule application, so an explanation can say which
  nodes the rule was applied to."
  [g p bindings]
  (cond
    (variable? p) (get bindings p)
    (term/compound? p)
    (let [cs (term/children p)
          ws (mapv #(witness g % bindings) cs)]
      (when (every? some? ws)
        (when-let [nid (eg/node-id g (term/make (term/operator p)
                                                (mapv (fn [c w] (eg/find g (witness-id c w))) cs ws)))]
          (into [nid] ws))))
    :else (eg/node-id g p)))
