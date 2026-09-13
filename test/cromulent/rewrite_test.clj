(ns cromulent.rewrite-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [cromulent.core :as eg]
            [cromulent.check :as check]
            [cromulent.extract :as ex]
            [cromulent.gen :as cg]
            [cromulent.pattern :as pat]
            [cromulent.rewrite :as rw]
            [cromulent.term :as term]))

(defn- constant-in
  "The numeric leaf in the class of id, if any."
  [g id]
  (some #(when (number? %) %) (:nodes (eg/eclass g id))))

(def egg-rules
  "The rule set of egg's README."
  [(rw/rule "commute-add" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "commute-mul" '[:* ?a ?b] '[:* ?b ?a])
   (rw/rule "add-0" '[:+ ?a 0] '?a)
   (rw/rule "mul-0" '[:* ?a 0] 0)
   (rw/rule "mul-1" '[:* ?a 1] '?a)])

(def sound-rules
  "Identities of the integers over :+ :* :neg, all of which terminate
  on a finite e-graph. Two are computed: they fold constants."
  (into egg-rules
        [(rw/rule "neg-neg" '[:neg [:neg ?a]] '?a)
         (rw/rule "fold-add" '[:+ ?a ?b]
                  (fn [g {:syms [?a ?b]}]
                    (let [x (constant-in g ?a), y (constant-in g ?b)]
                      (when (and x y) (+ x y)))))
         (rw/rule "fold-mul" '[:* ?a ?b]
                  (fn [g {:syms [?a ?b]}]
                    (let [x (constant-in g ?a), y (constant-in g ?b)]
                      (when (and x y) (* x y)))))]))

(def ac-rules
  [(rw/rule "comm" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "assoc" '[:+ [:+ ?a ?b] ?c] '[:+ ?a [:+ ?b ?c]])])

(defn- sum-of
  "A left-nested sum of n distinct atoms."
  [n]
  (reduce (fn [acc i] [:+ acc (keyword (str "a" i))]) :a0 (range 1 n)))

(defn- ok? [g]
  (let [vs (check/violations g)]
    (is (empty? vs) (pr-str vs))
    g))

;; ---------------------------------------------------------------------------
;; examples

(deftest rule-constructors
  (is (= {:name "n" :lhs '[:+ ?a 0] :rhs '?a} (rw/rule "n" '[:+ ?a 0] '?a)))
  (is (fn? (:when (rw/rule "n" '[:+ ?a 0] '?a :when (constantly true)))))
  (is (thrown? Exception (rw/rule "bad" '[:+ ?a 0] '?b)) "rhs variables must occur in lhs")
  (is (= ["c" "c-rev"] (map :name (rw/bidirectional "c" '[:+ ?a ?b] '[:+ ?b ?a]))))
  (is (thrown? Exception (rw/embiggen (eg/egraph) [(rw/rule "x" '?a '?a) (rw/rule "x" '?a '?a)]))
      "names must be distinct"))

(deftest egg-readme-simple
  ;; (+ 0 (* 1 a)) saturates and extracts to a with cost 1
  (doseq [scheduler [:simple :backoff]]
    (testing (name scheduler)
      (let [[g r] (eg/add (eg/egraph) [:+ 0 [:* 1 :a]])
            {:keys [egraph stop-reason iterations stats]} (rw/embiggen g egg-rules {:scheduler scheduler})]
        (ok? egraph)
        (is (= :saturated stop-reason))
        (is (= 3 iterations) "commute, then the identities, then a quiet iteration")
        (is (= iterations (count stats)))
        (is (= {:cost 1 :term :a} (ex/extract egraph r)))
        (is (= 3 (eg/class-count egraph)) "0, 1, and {a, 1*a, a*1, 0+a, a+0, ...}")
        (is (= 0 (reduce + (vals (:applied (last stats))))) "the last iteration applied nothing")))))

(deftest computed-rhs-and-guard
  (let [fold (rw/rule "fold" '[:+ ?a ?b]
                      (fn [g {:syms [?a ?b]}]
                        (let [x (constant-in g ?a), y (constant-in g ?b)]
                          (when (and x y) (+ x y)))))
        [g r] (eg/add (eg/egraph) [:+ [:+ 1 2] :x])
        res (rw/embiggen g [fold])]
    (ok? (:egraph res))
    (is (= :saturated (:stop-reason res)))
    (is (= 3 (constant-in (:egraph res) (second (eg/add g [:+ 1 2])))) "1+2 folds to 3")
    (is (nil? (constant-in (:egraph res) r)) "x is not a constant, so the rhs declined"))
  (let [div (rw/rule "div-self" '[:/ ?a ?a] 1
                     :when (fn [g {:syms [?a]}] (not= 0 (constant-in g ?a))))
        [g ok] (eg/add (eg/egraph) [:/ :x :x])
        [g bad] (eg/add g [:/ 0 0])
        res (rw/embiggen g [div])
        one (second (eg/add (:egraph res) 1))]
    (ok? (:egraph res))
    (is (= one (eg/find (:egraph res) ok)) "x/x = 1")
    (is (not= one (eg/find (:egraph res) bad)) "the guard kept 0/0 out")))

(deftest guard-sees-the-search-snapshot
  ;; r1 adds a :g node; r2 is guarded on there being no :g node. Under
  ;; snapshot semantics both fire in the same iteration regardless of
  ;; rule order.
  (let [r1 (rw/rule "r1" '[:f ?a] '[:g ?a])
        r2 (rw/rule "r2" '[:f ?a] '[:h ?a] :when (fn [g _] (not (contains? (:by-op g) :g))))
        [g f] (eg/add (eg/egraph) [:f :x])]
    (doseq [rules [[r1 r2] [r2 r1]]]
      (let [{:keys [egraph stats]} (rw/embiggen g rules {:iter-limit 1})]
        (is (= {"r1" 1 "r2" 1} (:applied (first stats))))
        (is (= (eg/find egraph f) (cg/id-of egraph [:h :x])))))))

(deftest limits
  (let [[g _] (eg/add (eg/egraph) (sum-of 6))]
    (is (= :iter-limit (:stop-reason (rw/embiggen g ac-rules {:iter-limit 1}))))
    (is (= 1 (:iterations (rw/embiggen g ac-rules {:iter-limit 1}))))
    (is (= :node-limit (:stop-reason (rw/embiggen g ac-rules {:node-limit 20}))))
    (let [res (rw/embiggen g ac-rules {:time-limit-ms -1})]
      (is (= :time-limit (:stop-reason res)))
      (is (= 0 (:iterations res)) "the limit is checked before every iteration, including the first"))
    (is (= 0 (:iterations (rw/embiggen g ac-rules {:iter-limit 0}))))))

(deftest ac-blowup-matches-the-formula
  ;; ../design/ac-problem.md section 1: a sum of n atoms under
  ;; commutativity and associativity has 2^n - 1 classes and
  ;; 3^n - 2^(n+1) + 1 compound e-nodes (plus the n leaves).
  (let [n 5
        [g _] (eg/add (eg/egraph) (sum-of n))
        {:keys [egraph stop-reason]} (rw/embiggen g ac-rules {:scheduler :simple})]
    (ok? egraph)
    (is (= :saturated stop-reason))
    (is (= 31 (eg/class-count egraph)))
    (is (= (+ 180 n) (eg/node-count egraph)))))

(deftest backoff-bans-and-recovers
  (let [[g _] (eg/add (eg/egraph) (sum-of 5))
        simple (rw/embiggen g ac-rules {:scheduler :simple})
        backoff (rw/embiggen g ac-rules {:scheduler :backoff :match-limit 4 :ban-length 2})]
    (is (some (comp seq :banned) (:stats backoff)) "some rule was banned at some point")
    (is (= :saturated (:stop-reason backoff)))
    (is (< (:iterations simple) (:iterations backoff)) "bans cost iterations")
    (is (= (eg/node-count (:egraph simple)) (eg/node-count (:egraph backoff))))
    (is (= (eg/class-count (:egraph simple)) (eg/class-count (:egraph backoff))))))

(deftest timeline
  (let [[g _] (eg/add (eg/egraph) [:+ 0 [:* 1 :a]])
        {:keys [timeline iterations egraph]} (rw/embiggen g egg-rules {:timeline? true})]
    (is (= (inc iterations) (count timeline)))
    (is (= g (first timeline)) "the input, rebuilt")
    (is (= egraph (last timeline)))
    (is (nil? (:timeline (rw/embiggen g egg-rules))))))

(deftest custom-scheduler
  ;; a scheduler that only ever runs the first rule
  (let [first-only {:init (fn [rules _] (:name (first rules)))
                    :search (fn [state _ rule search] [state (if (= state (:name rule)) (search) [])])
                    :can-stop (fn [state _] [state true])}
        [g _] (eg/add (eg/egraph) [:+ 0 [:* 1 :a]])
        {:keys [stats]} (rw/embiggen g egg-rules {:scheduler first-only})]
    (is (every? #(= 0 (get (:applied %) "commute-mul")) stats))
    (is (pos? (get (:applied (first stats)) "commute-add")))))

;; ---------------------------------------------------------------------------
;; properties

(def ^:private num-tests 200)

(deftest embiggen-keeps-invariants
  ;; random, unsound rules over random scripts with unions: whatever is
  ;; merged, the result is a well-formed e-graph
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops cg/script-gen, rules cg/rules-gen, scheduler (gen/elements [:simple :backoff])]
               (let [g (:egraph (cg/run-script (eg/egraph) ops))
                     {:keys [egraph iterations stop-reason]}
                     (rw/embiggen g rules {:iter-limit 3 :node-limit 300 :scheduler scheduler
                                           :match-limit 5 :ban-length 2})]
                 (and (empty? (check/violations egraph))
                      (<= iterations 3)
                      (contains? #{:saturated :iter-limit :node-limit} stop-reason)))))]
    (is (:pass? res) (pr-str res))))

(defn- meaning-preserved?
  "Under env, every node of every class evaluates to the value of the
  class's extracted term."
  [g env]
  (let [ex (ex/extractor g)
        roots (eg/roots g)
        value (into {} (map (fn [r] [r (cg/evaluate (:term (ex r)) env)])) roots)
        node-value (fn [node]
                     (if (term/compound? node)
                       (cg/evaluate (term/make (term/operator node)
                                               (mapv #(get value (eg/find g %)) (term/children node)))
                                    env)
                       (cg/evaluate node env)))]
    (every? (fn [r] (every? #(= (get value r) (node-value %)) (eg/nodes g r))) roots)))

(deftest sound-rules-preserve-meaning
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ts cg/terms-gen, env (gen/map (gen/elements [:a :b :c]) gen/small-integer)]
               (let [env (merge {:a 0 :b 0 :c 0} env)
                     g (:egraph (cg/add-terms (eg/egraph) ts))
                     {:keys [egraph]} (rw/embiggen g sound-rules {:iter-limit 4 :node-limit 500 :scheduler :simple})]
                 (and (empty? (check/violations egraph))
                      (meaning-preserved? egraph env)))))]
    (is (:pass? res) (pr-str res))))

(defn- closed-under?
  "Every match of every rule instantiates to its own class without
  adding a node."
  [g rules]
  (every? (fn [{:keys [lhs rhs]}]
            (every? (fn [{:keys [class bindings]}]
                      (let [p (if (fn? rhs) (rhs g bindings) rhs)]
                        (or (nil? p)
                            (let [[g' id] (pat/instantiate g p bindings)]
                              (and (= (eg/find g' id) class)
                                   (= (:next-id g') (:next-id g)))))))
                    (pat/ematch g lhs)))
          rules))

(deftest saturated-means-closed
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ts cg/terms-gen]
               (let [g (:egraph (cg/add-terms (eg/egraph) ts))
                     {:keys [egraph stop-reason]} (rw/embiggen g sound-rules {:iter-limit 30 :node-limit 5000 :scheduler :simple})]
                 (and (= :saturated stop-reason)
                      (closed-under? egraph sound-rules)
                      (let [again (rw/embiggen egraph sound-rules {:scheduler :simple})]
                        (and (= :saturated (:stop-reason again))
                             (= 1 (:iterations again))
                             (= egraph (:egraph again))))))))]
    (is (:pass? res) (pr-str res))))

(deftest schedulers-agree
  ;; when both saturate, backoff reaches the same e-graph as simple:
  ;; same counts, same partition of the input terms
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ts cg/terms-gen]
               (let [{:keys [egraph terms]} (cg/add-terms (eg/egraph) ts)
                     opts {:iter-limit 60 :node-limit 5000}
                     a (rw/embiggen egraph sound-rules (assoc opts :scheduler :simple))
                     b (rw/embiggen egraph sound-rules (assoc opts :scheduler :backoff :match-limit 3 :ban-length 2))
                     partition (fn [g] (set (vals (group-by #(cg/id-of g %) terms))))]
                 (and (= :saturated (:stop-reason a) (:stop-reason b))
                      (= (eg/node-count (:egraph a)) (eg/node-count (:egraph b)))
                      (= (eg/class-count (:egraph a)) (eg/class-count (:egraph b)))
                      (= (partition (:egraph a)) (partition (:egraph b)))))))]
    (is (:pass? res) (pr-str res))))

(deftest searcher-rules
  ;; a searcher finds matches by reading the e-graph directly: here,
  ;; every class holding a number above 10 is rewritten to [:big]
  (let [big (rw/rule "big"
                     (fn [g]
                       (into [] (keep (fn [r]
                                        (when (some #(and (number? %) (> % 10)) (eg/nodes g r))
                                          {:class r :bindings {}})))
                             (eg/roots g)))
                     [:big])
        [g a] (eg/add (eg/egraph) [:+ 5 50])
        {:keys [egraph stop-reason]} (rw/embiggen g [big])
        fifty (second (eg/add egraph 50))
        five (second (eg/add egraph 5))]
    (ok? egraph)
    (is (= :saturated stop-reason))
    (is (= (eg/find egraph fifty) (cg/id-of egraph [:big])))
    (is (not= (eg/find egraph five) (cg/id-of egraph [:big])))))

(deftest a-match-may-carry-its-own-rhs
  ;; one rule, a different right-hand side per class: every class
  ;; holding a number n also holds [:num n]
  (let [tag (rw/rule "tag"
                     (fn [g]
                       (into [] (keep (fn [r]
                                        (when-let [n (some #(when (number? %) %) (eg/nodes g r))]
                                          {:class r :bindings {'?r r} :rhs [:num n '?r]})))
                             (eg/roots g)))
                     nil)
        [g _] (eg/add (eg/egraph) [:+ 5 50])
        {:keys [egraph stop-reason iterations]} (rw/embiggen g [tag])]
    (ok? egraph)
    (is (= :saturated stop-reason))
    (is (= 2 iterations) "one iteration applies, the next finds nothing new")
    (is (= (cg/id-of egraph 5) (cg/id-of egraph [:num 5 5])))
    (is (= (cg/id-of egraph 50) (cg/id-of egraph [:num 50 50])))
    (is (= 5 (eg/node-count egraph)) "5, 50, their sum, and the two tags: nothing else")))

(deftest failures-name-the-rule
  (let [boom (rw/rule "boom" '[:+ ?a ?b] (fn [_ _] (throw (ex-info "no" {:why :test}))))
        [g _] (eg/add (eg/egraph) [:+ 1 2])
        e (try (rw/embiggen g [boom]) nil (catch Exception e e))]
    (is (some? e))
    (is (= "boom" (:rule (ex-data e))))
    (is (= :test (:why (ex-data e))))))
