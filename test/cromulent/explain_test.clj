(ns cromulent.explain-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [cromulent.core :as eg]
            [cromulent.explain :as x]
            [cromulent.gen :as cg]
            [cromulent.derivation :as derivation]
            [cromulent.rewrite :as rw]
            [cromulent.smoke :as smoke]))

(defn- constant-in [g id]
  (some #(when (number? %) %) (eg/nodes g id)))

(def readme-rules
  [(rw/rule "commute-add" '[:+ ?a ?b] '[:+ ?b ?a])
   (rw/rule "commute-mul" '[:* ?a ?b] '[:* ?b ?a])
   (rw/rule "add-0" '[:+ ?a 0] '?a)
   (rw/rule "mul-1" '[:* ?a 1] '?a)
   (rw/rule "fold" '[:+ ?a ?b]
            (fn [g {:syms [?a ?b]}]
              (let [x (constant-in g ?a), y (constant-in g ?b)]
                (when (and x y) (+ x y)))))
   (rw/rule "div-self" '[:/ ?a ?a] 1
            :when (fn [g {:syms [?a]}] (not= 0 (constant-in g ?a))))])

(defn- every-member-explained?
  "Every id of every class has a derivation, accepted by the checker, that
  the term it was born as equals the term its root was born as."
  [g rules]
  (every? (fn [r]
            (every? (fn [m]
                      (derivation/derives? (x/explain g m r) rules (x/term g m) (x/term g r)))
                    (:members (eg/eclass g r))))
          (eg/roots g)))

(deftest the-proposal's-example
  (let [g (eg/egraph {:explain? true})
        [g a] (eg/add g :a)
        [g b] (eg/add g :b)
        [g fa] (eg/add g [:f :a])
        [g fb] (eg/add g [:f :b])
        [g _] (eg/union g a b "a = b")
        g (eg/rebuild g)]
    (is (= {:births [:a :b [:f 0] [:f 1]] :unions [[0 1 "a = b"] [2 3 :congruence]]}
           (:journal g)))
    (is (= [:cong :f [[:asserted :a :b "a = b"]]] (x/explain g fa fb)))
    (is (= [:sym [:cong :f [[:asserted :a :b "a = b"]]]] (x/explain g fb fa)))
    (is (= {:ok? true :lhs [:f :a] :rhs [:f :b]
            :trusted [{:asserted "a = b" :lhs :a :rhs :b}]}
           (derivation/check (x/explain g fa fb) [])))))

(deftest without-a-journal
  (testing "nothing is recorded, and explaining says why it cannot"
    (let [[g _] (eg/add (eg/egraph) [:f :a])]
      (is (nil? (:journal g)))
      (is (thrown-with-msg? Exception #"no journal" (x/explain g 0 1))))))

(deftest the-readme-run
  (let [[g _] (eg/add (eg/egraph {:explain? true}) [:+ 0 [:* 1 :a]])
        [g _] (eg/add g [:+ 2 3])
        [g _] (eg/add g [:/ [:+ 2 3] [:+ 3 2]])
        {g :egraph} (rw/embiggen g readme-rules {})]
    (testing "pattern rules only: every step checked, nothing trusted"
      (let [p (x/explain-terms g [:+ 0 [:* 1 :a]] :a)]
        (is (= [:trans
                [:rule "commute-add" '{?a 0 ?b [:* 1 :a]}]
                [:rule "add-0" '{?a [:* 1 :a]}]
                [:rule "commute-mul" '{?a 1 ?b :a}]
                [:rule "mul-1" '{?a :a}]]
               p))
        (is (= {:ok? true :lhs [:+ 0 [:* 1 :a]] :rhs :a :trusted []}
               (derivation/check p readme-rules)))))
    (testing "a computed right-hand side is a trusted step"
      (let [p (x/explain-terms g [:+ 2 3] 5)]
        (is (derivation/derives? p readme-rules [:+ 2 3] 5))
        (is (= [{:computed "fold" :lhs [:+ 2 3] :rhs 5}] (:trusted (derivation/check p readme-rules))))))
    (testing "a guarded rule is checked, and its guard reported as trusted"
      (let [p (x/explain-terms g [:/ [:+ 2 3] [:+ 3 2]] 1)
            {:keys [ok? trusted]} (derivation/check p readme-rules)]
        (is ok?)
        (is (derivation/derives? p readme-rules [:/ [:+ 2 3] [:+ 3 2]] 1))
        (is (some :guard trusted))))
    (testing "terms in different classes have no explanation"
      (is (nil? (x/explain-terms g :a 5))))
    (is (every-member-explained? g readme-rules))))

(deftest analysis-merges-are-asserted
  (let [g (eg/egraph {:explain? true :analysis smoke/const-fold})
        [g _] (eg/add g [:+ 1 [:* 2 3]])
        g (eg/rebuild g)
        p (x/explain-terms g [:+ 1 [:* 2 3]] 7)]
    (is (derivation/derives? p [] [:+ 1 [:* 2 3]] 7))
    (is (every? #(contains? % :asserted) (:trusted (derivation/check p []))))
    (is (every-member-explained? g []))))

(deftest the-checker-refuses
  (let [rules readme-rules]
    (testing "a binding changed"
      (let [r (derivation/check [:rule "add-0" '{?a :b}] rules)]
        (is (:ok? r))
        (is (not (derivation/derives? [:rule "add-0" '{?a :b}] rules [:+ :a 0] :a)))))
    (testing "a chain whose links do not meet, naming the link"
      (let [r (derivation/check [:trans [:rule "add-0" '{?a :a}] [:rule "mul-1" '{?a :b}]] rules)]
        (is (= false (:ok? r)))
        (is (= [2] (:path r)))
        (is (= :a (:expected r)))))
    (testing "an unknown rule, inside a congruence"
      (let [r (derivation/check [:cong :f [[:refl :a] [:rule "nope" {}]]] rules)]
        (is (= false (:ok? r)))
        (is (= [2 1] (:path r)))))
    (testing "a variable the step does not bind"
      (is (= false (:ok? (derivation/check [:rule "commute-add" '{?a 1}] rules)))))
    (testing "a computed rule's pattern step is not taken"
      (is (= false (:ok? (derivation/check [:rule "fold" '{?a 1 ?b 2}] rules)))))
    (testing "a malformed step is refused, not thrown"
      (doseq [[d path] [[[:sym] []] [[:refl] []] [[:refl :a :b] []] [[:trans] []]
                        [[:cong :f :x] []] [[:rule "add-0"] []] [[:rule "add-0" 3] []]
                        [[:computed "fold" 1] []] [[:asserted :a :b] []]
                        [[:nope :a] []] [:refl []] [[] []] [nil []]
                        [[:trans [:refl :a] [:sym]] [2]] [[:cong :f [[:refl :a] [:cong :g]]] [2 1]]]]
        (let [r (derivation/check d rules)]
          (is (= false (:ok? r)) (pr-str d))
          (is (= path (:path r)) (pr-str d))
          (is (string? (:problem r)) (pr-str d)))))))

;; ---------------------------------------------------------------------------
;; properties

(deftest journaling-changes-nothing-else
  (let [res (tc/quick-check
             40
             (prop/for-all [ts cg/terms-gen, rules cg/rules-gen, scheduler (gen/elements [:simple :backoff])]
               (let [opts {:iter-limit 4 :node-limit 400 :scheduler scheduler :match-limit 8 :ban-length 2}
                     run (fn [g] (rw/embiggen (:egraph (cg/add-terms g ts)) rules opts))
                     a (run (eg/egraph))
                     b (run (eg/egraph {:explain? true}))
                     shape (fn [res] [(:stop-reason res) (mapv (juxt :nodes :classes :matches :applied) (:stats res))])]
                 (and (= (shape a) (shape b))
                      (= (:uf (:egraph a)) (:uf (:egraph b)))))))]
    (is (:pass? res) (pr-str res))))

(deftest every-equality-has-a-checked-derivation
  (testing "random scripts of adds and asserted unions, then random rules, sound or not"
    (let [res (tc/quick-check
               60
               (prop/for-all [ops cg/script-gen, rules cg/rules-gen, scheduler (gen/elements [:simple :backoff])]
                 (let [g (:egraph (cg/run-script (eg/egraph {:explain? true}) ops))
                       {g :egraph} (rw/embiggen g rules {:iter-limit 3 :node-limit 300 :scheduler scheduler
                                                         :match-limit 5 :ban-length 2})]
                   (every-member-explained? g rules))))]
      (is (:pass? res) (pr-str res))))
  (testing "between ground terms, and none between terms the e-graph keeps apart"
    (let [res (tc/quick-check
               60
               (prop/for-all [ops cg/script-gen, rules cg/rules-gen]
                 (let [{g :egraph terms :terms} (cg/run-script (eg/egraph {:explain? true}) ops)
                       {g :egraph} (rw/embiggen g rules {:iter-limit 3 :node-limit 300 :scheduler :simple})
                       ts (vec (take 12 terms))]
                   (every? (fn [[s t]]
                             (let [p (x/explain-terms g s t)]
                               (if (= (cg/id-of g s) (cg/id-of g t))
                                 (derivation/derives? p rules s t)
                                 (nil? p))))
                           (for [s ts, t ts] [s t])))))]
      (is (:pass? res) (pr-str res)))))
