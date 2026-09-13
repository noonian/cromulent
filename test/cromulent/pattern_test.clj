(ns cromulent.pattern-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [cromulent.core :as eg]
            [cromulent.check :as check]
            [cromulent.gen :as cg]
            [cromulent.pattern :as pat]
            [cromulent.term :as term]))

(defn- ids
  "Map of ground term -> root id, for readable assertions."
  [g & ts]
  (into {} (map (fn [t] [t (cg/id-of g t)])) ts))

(deftest variables-and-groundness
  (is (pat/variable? '?a))
  (is (not (pat/variable? '?)))
  (is (not (pat/variable? :a)))
  (is (= '#{?a ?b} (pat/variables '[:+ ?a [:* ?b ?a]])))
  (is (pat/ground? [:+ 1 :x])))

(deftest egg-readme-match
  (let [g (-> (eg/egraph)
              (eg/add [:* :a 2]) first
              (eg/add [:<< :a 1]) first
              (eg/add [:* :b 2]) first)
        {a :a, b :b, a2 [:* :a 2], b2 [:* :b 2]} (ids g :a :b [:* :a 2] [:* :b 2])]
    (is (= #{{:class a2 :bindings {'?x a}}
             {:class b2 :bindings {'?x b}}}
           (set (pat/ematch g '[:* ?x 2]))))
    (is (= [] (pat/ematch g '[:* ?x 3])) "no class holds a 3")
    (is (= [] (pat/ematch g '[:+ ?x 2])) "the index rules out :+ without scanning")
    (is (= [{'?x a}] (pat/match-class g '[:* ?x 2] a2)))
    (is (= [] (pat/match-class g '[:* ?x 2] a)))))

(deftest repeated-variables
  (let [g (-> (eg/egraph) (eg/add [:+ :a :a]) first (eg/add [:+ :a :b]) first)
        {aa [:+ :a :a], a :a} (ids g [:+ :a :a] :a)]
    (is (= [{:class aa :bindings {'?x a}}] (pat/ematch g '[:+ ?x ?x])))
    (is (= 2 (count (pat/ematch g '[:+ ?x ?y]))))))

(deftest ground-and-variable-patterns
  (let [g (-> (eg/egraph) (eg/add [:+ 1 :x]) first)]
    (is (= [{:class (cg/id-of g 1) :bindings {}}] (pat/ematch g 1)))
    (is (= [] (pat/ematch g 7)))
    (is (= (set (eg/roots g)) (set (map :class (pat/ematch g '?any)))) "a bare variable matches every class")))

(deftest matching-through-union
  ;; a*2 = a<<1; afterwards both spellings of (a*2)/2 match the one merged class
  (let [g (-> (eg/egraph)
              (eg/add [:/ [:* :a 2] 2]) first
              (eg/add [:/ [:<< :a 1] 2]) first)
        [g _] (eg/union g (cg/id-of g [:* :a 2]) (cg/id-of g [:<< :a 1]))
        g (eg/rebuild g)
        d (cg/id-of g [:/ [:* :a 2] 2])
        a (cg/id-of g :a)]
    (is (empty? (check/violations g)))
    (is (= [{:class d :bindings {'?a a}}] (pat/ematch g '[:/ [:* ?a 2] 2])))
    (is (= [{:class d :bindings {'?a a}}] (pat/ematch g '[:/ [:<< ?a 1] 2])))
    (is (= [{:class d :bindings {'?a a, '?two (cg/id-of g 2)}}] (pat/ematch g '[:/ [:<< ?a 1] ?two]))
        "a variable in place of the constant binds to the class of 2")))

(deftest index-follows-unions
  (let [g (-> (eg/egraph) (eg/add [:+ :a 1]) first (eg/add [:* :b 1]) first)
        [g r] (eg/union g (cg/id-of g [:+ :a 1]) (cg/id-of g [:* :b 1]))]
    (is (= #{r} (get (:by-op g) :+)) "exact even before rebuild")
    (is (= #{r} (get (:by-op g) :*)))
    (is (empty? (check/violations (eg/rebuild g))))))

(deftest instantiate-reuses-and-adds
  (let [g (-> (eg/egraph) (eg/add [:* :a 2]) first)
        a (cg/id-of g :a)
        [g s] (pat/instantiate g '[:<< ?a 1] {'?a a})
        [g s2] (pat/instantiate g '[:<< ?a 1] {'?a a})]
    (is (= s s2) "instantiating twice adds nothing")
    (is (= s (cg/id-of g [:<< :a 1])))
    (is (= 5 (eg/class-count g)) ":a 2 1 a*2 a<<1")
    (is (thrown? Exception (pat/instantiate g '[:<< ?b 1] {'?a a})))
    (let [[g' seven] (pat/instantiate g 7 {})]
      (is (= seven (cg/id-of g' 7)) "a ground leaf pattern is just the leaf")
      (is (= 6 (eg/class-count g'))))))

;; ---------------------------------------------------------------------------
;; properties

(defn tree-match
  "Bindings (variable -> ground subterm) under which pattern p matches
  ground term t, or nil. The plain tree-matching reference."
  [p t binds]
  (cond
    (pat/variable? p)
    (if-let [b (get binds p)] (when (= b t) binds) (assoc binds p t))

    (term/compound? p)
    (when (and (term/compound? t)
               (= (term/operator p) (term/operator t))
               (= (term/arity p) (term/arity t)))
      (reduce (fn [b [pc tc]] (or (tree-match pc tc b) (reduced nil)))
              binds
              (map vector (term/children p) (term/children t))))

    :else
    (when (= p t) binds)))

(def ^:private num-tests 200)

(deftest ematch-is-sound
  ;; every reported match instantiates back to the class it was found in
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops cg/script-gen, p cg/pattern-gen]
               (let [g (:egraph (cg/run-script (eg/egraph) ops))]
                 (every? (fn [{:keys [class bindings]}]
                           (and (eg/root? g class)
                                (every? #(eg/root? g %) (vals bindings))
                                (= (pat/variables p) (set (keys bindings)))
                                (let [[g' id] (pat/instantiate g p bindings)]
                                  (and (= (eg/find g' id) class)
                                       (= (:next-id g') (:next-id g))))))
                         (pat/ematch g p)))))]
    (is (:pass? res) (pr-str res))))

(deftest ematch-is-complete
  ;; every tree match over the ground terms appears among the matches
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops cg/script-gen, p cg/pattern-gen]
               (let [{:keys [egraph terms]} (cg/run-script (eg/egraph) ops)
                     found (set (pat/ematch egraph p))]
                 (every? (fn [t]
                           (if-let [b (tree-match p t {})]
                             (contains? found {:class (cg/id-of egraph t)
                                               :bindings (into {} (map (fn [[v s]] [v (cg/id-of egraph s)])) b)})
                             true))
                         terms))))]
    (is (:pass? res) (pr-str res))))

(deftest ematch-has-no-duplicates
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops cg/script-gen, p cg/pattern-gen]
               (let [ms (pat/ematch (:egraph (cg/run-script (eg/egraph) ops)) p)]
                 (= (count ms) (count (set ms))))))]
    (is (:pass? res) (pr-str res))))
