(ns cromulent.smoke
  "Runtime-stable facts about a few fixed runs, the same on the JVM,
  on Jolt and in ClojureScript: class and node counts, costs,
  iterations, stop reasons, per-rule counts, and extracted terms where
  the minimum is unique. Ties break on class ids, and ids follow hash
  iteration order, which differs per runtime, so no id and no tied
  term is asserted. `checks` is plain data: cromulent.smoke-test
  asserts it under clojure.test, and orrery's node build prints it
  (`npx shadow-cljs compile smoke && node target/smoke.js`)."
  (:require [cromulent.check :as check]
            [cromulent.core :as eg]
            [cromulent.extract :as ex]
            [cromulent.pattern :as pat]
            [cromulent.rewrite :as rw]
            [cromulent.term :as term]))

(def egg-rules
  "The rule set of egg's README."
  [(rw/rule "commute-add" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "commute-mul" '[:* ?a ?b] '[:* ?b ?a])
   (rw/rule "add-0" '[:+ ?a 0] '?a)
   (rw/rule "mul-0" '[:* ?a 0] 0)
   (rw/rule "mul-1" '[:* ?a 1] '?a)])

(def ac-rules
  [(rw/rule "comm" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "assoc" '[:+ [:+ ?a ?b] ?c] '[:+ ?a [:+ ?b ?c]])])

(defn sum-of
  "A left-nested sum of n distinct atoms."
  [n]
  (reduce (fn [acc i] [:+ acc (keyword (str "a" i))]) :a0 (range 1 n)))

(def const-fold
  "The constant-folding analysis of core_test, a flat lattice
  nil < number < :conflict."
  {:name :const-fold
   :make (fn [g node _]
           (if (term/compound? node)
             (let [ds (map #(eg/data g % :const-fold) (term/children node))]
               (cond
                 (some #{:conflict} ds) :conflict
                 (every? number? ds) (case (term/operator node)
                                       :+ (reduce + ds)
                                       :* (reduce * ds)
                                       :neg (- (first ds))
                                       nil)
                 :else nil))
             (when (number? node) node)))
   :merge (fn [_ a b]
            (cond (nil? a) b
                  (nil? b) a
                  (= a b) a
                  :else :conflict))
   :modify (fn [g id]
             (let [d (eg/data g id :const-fold)]
               (if (number? d)
                 (let [[g cid] (eg/add g d)]
                   (first (eg/union g id cid)))
                 g)))})

(defn- expensive-mul [node child-costs]
  (+ (if (and (term/compound? node) (= :* (term/operator node))) 10 1)
     (reduce + child-costs)))

(defn- fact [name expected actual]
  {:name name :expected expected :actual actual :ok? (= expected actual)})

(defn checks
  "A vector of {:name :expected :actual :ok?}."
  []
  (let [;; egg's README: a*2 = a<<1, so (a*2)/2 = (a<<1)/2 by congruence
        g (eg/egraph)
        [g m]  (eg/add g [:* :a 2])
        [g s]  (eg/add g [:<< :a 1])
        [g dm] (eg/add g [:/ [:* :a 2] 2])
        [g ds] (eg/add g [:/ [:<< :a 1] 2])
        before (= (eg/find g dm) (eg/find g ds))
        [g _]  (eg/union g m s)
        g (eg/rebuild g)
        ;; the README rule set on 0 + 1·a
        [g2 r2] (eg/add (eg/egraph) [:+ 0 [:* 1 :a]])
        simple  (rw/embiggen g2 egg-rules {:scheduler :simple :timeline? true})
        backoff (rw/embiggen g2 egg-rules {:scheduler :backoff})
        ;; the blowup: a sum of five atoms under commutativity and associativity
        [g5 r5] (eg/add (eg/egraph) (sum-of 5))
        ac-simple  (rw/embiggen g5 ac-rules {:scheduler :simple})
        ac-backoff (rw/embiggen g5 ac-rules {:scheduler :backoff :match-limit 4 :ban-length 2})
        ;; taste
        [g3 m3] (eg/add (eg/egraph) [:* :a 2])
        [g3 s3] (eg/add g3 [:<< :a 1])
        [g3 _]  (eg/union g3 m3 s3)
        g3 (eg/rebuild g3)
        ;; an analysis
        g4 (eg/egraph {:analysis const-fold})
        [g4 r4] (eg/add g4 [:+ 1 [:* 2 3]])
        g4 (eg/rebuild g4)
        [g4 seven] (eg/add g4 7)]
    [(fact "congruence: the quotients differ before the union" false before)
     (fact "congruence: (a*2)/2 = (a<<1)/2 after union and rebuild" true (= (eg/find g dm) (eg/find g ds)))
     (fact "congruence: class count" 5 (eg/class-count g))
     (fact "congruence: node count" 6 (eg/node-count g))
     (fact "congruence: one canonical quotient node" 1 (count (eg/nodes g dm)))
     (fact "congruence: invariants hold" true (empty? (check/violations g)))
     (fact "ematch [:* ?x 2] finds a*2 once, ?x bound to a's class"
           [1 true]
           (let [ms (pat/ematch g '[:* ?x 2])]
             [(count ms) (= (get-in (first ms) [:bindings '?x]) (eg/lookup g :a))]))
     (fact "egg rules, simple: stop reason" :saturated (:stop-reason simple))
     (fact "egg rules, simple: iterations" 3 (:iterations simple))
     (fact "egg rules, simple: timeline length" 4 (count (:timeline simple)))
     (fact "egg rules, simple: class count" 3 (eg/class-count (:egraph simple)))
     (fact "egg rules, simple: extraction, a unique minimum" {:cost 1 :term :a} (ex/extract (:egraph simple) r2))
     (fact "egg rules, simple: matches per rule per iteration"
           [{"commute-add" 1 "commute-mul" 1 "add-0" 0 "mul-0" 0 "mul-1" 0}
            {"commute-add" 2 "commute-mul" 2 "add-0" 1 "mul-0" 0 "mul-1" 1}
            {"commute-add" 2 "commute-mul" 2 "add-0" 1 "mul-0" 0 "mul-1" 1}]
           (mapv :matches (:stats simple)))
     (fact "egg rules, simple: applied per rule per iteration"
           [{"commute-add" 1 "commute-mul" 1 "add-0" 0 "mul-0" 0 "mul-1" 0}
            {"commute-add" 0 "commute-mul" 0 "add-0" 1 "mul-0" 0 "mul-1" 1}
            {"commute-add" 0 "commute-mul" 0 "add-0" 0 "mul-0" 0 "mul-1" 0}]
           (mapv :applied (:stats simple)))
     (fact "egg rules, backoff: the same result"
           [:saturated 3 3 {:cost 1 :term :a}]
           [(:stop-reason backoff) (:iterations backoff) (eg/class-count (:egraph backoff)) (ex/extract (:egraph backoff) r2)])
     (fact "sum of five, simple: stop reason and iterations" [:saturated 7] [(:stop-reason ac-simple) (:iterations ac-simple)])
     (fact "sum of five, simple: classes" 31 (eg/class-count (:egraph ac-simple)))
     (fact "sum of five, simple: nodes, 180 compound and 5 atoms" 185 (eg/node-count (:egraph ac-simple)))
     (fact "sum of five, simple: nodes after each iteration" [19 45 98 162 187 185 185] (mapv :nodes (:stats ac-simple)))
     (fact "sum of five, simple: classes after each iteration" [12 22 35 39 33 31 31] (mapv :classes (:stats ac-simple)))
     (fact "sum of five, simple: invariants hold" true (empty? (check/violations (:egraph ac-simple))))
     (fact "sum of five, simple: every arrangement costs 9 (a tie; the term is not asserted)" 9 (:cost (ex/extract (:egraph ac-simple) r5)))
     (fact "sum of five, backoff: same counts, more iterations, a ban seen"
           [31 185 :saturated true true]
           [(eg/class-count (:egraph ac-backoff)) (eg/node-count (:egraph ac-backoff)) (:stop-reason ac-backoff)
            (< (:iterations ac-simple) (:iterations ac-backoff))
            (boolean (some (comp seq :banned) (:stats ac-backoff)))])
     (fact "taste: a*2 = a<<1 costs 3 under ast-size (a tie; the term is not asserted)" 3 (:cost (ex/extract g3 m3)))
     (fact "taste: a cost that charges * ten picks the shift" {:cost 3 :term [:<< :a 1]} (ex/extract g3 m3 expensive-mul))
     (fact "analysis: 1 + 2*3 folds to 7 and joins the class of 7"
           [7 true]
           [(eg/data g4 r4 :const-fold) (= (eg/find g4 r4) (eg/find g4 seven))])
     (fact "packed keys: the ceiling is 2^53 - 1, exact everywhere" 9007199254740991 (eg/packed-key {:+ 2047} :+ 2097151 2097151))
     (fact "packed keys: a key round-trips through the memo"
           true
           (let [[g id] (eg/add (eg/egraph) [:+ :x :y])]
             (= id (eg/lookup g (first (eg/nodes g id))))))]))
