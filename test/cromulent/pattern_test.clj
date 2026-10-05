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

(defn- flat
  "[matches found] of p in g as `ematch-flat` gives them: the matches
  it wrote, each [class binding ...], as a set, and how many it found."
  [g p since]
  (let [[^longs buf n found] (pat/ematch-flat g p (long-array 4) since)
        stride (inc (count (:vars (pat/compile p))))]
    [(set (for [m (range n)] (mapv #(aget buf (+ (* m stride) %)) (range stride)))) found]))

(deftest fresh-matches
  ;; f(g(x)) and f(g(y)), and a g(z) and an f(w) that do not meet, all
  ;; of epoch 0: two matches of f(g(?a))
  (let [p '[:f [:g ?a]]
        g (reduce (fn [g t] (first (eg/add g t))) (eg/egraph) [[:f [:g :x]] [:f [:g :y]] [:g :z] [:f :w]])
        {x :x, y :y, z :z, w :w, fgx [:f [:g :x]], fgy [:f [:g :y]], gz [:g :z], fw [:f :w]}
        (ids g :x :y :z :w [:f [:g :x]] [:f [:g :y]] [:g :z] [:f :w])]
    (is (= [#{[fgx x] [fgy y]} 2] (flat g p nil)) "every match, when no epoch is given")
    (is (= [#{} 2] (flat g p 0)) "nothing has changed since epoch 0")
    ;; epoch 1: w = g(z), so f(w) reads f(g(z)) now; and f(g(v)) is new
    (let [g1 (eg/rebuild (first (eg/union (eg/next-epoch g) w gz)))
          [g1 fgv] (eg/add g1 [:f [:g :v]])
          v (eg/lookup g1 :v)]
      (is (empty? (check/violations g1)))
      (is (= 4 (count (pat/ematch g1 p))))
      (is (= [#{[(eg/find g1 fw) z] [fgv v]} 4] (flat g1 p 0))
          "the match a union made and the match of new nodes; the two old ones are counted and not written")
      (is (= [#{} 4] (flat g1 p 1)) "and after epoch 1, none"))))

(deftest a-leaf-that-moved-makes-a-match-fresh
  (let [p '[:f 0]
        [g fw] (eg/add (eg/egraph) [:f :w])
        [g zero] (eg/add g 0)
        g1 (eg/rebuild (first (eg/union (eg/next-epoch g) (eg/lookup g :w) zero)))]
    (is (= [#{} 0] (flat g p 0)))
    (is (= [#{[fw]} 1] (flat g1 p 0)) "f(w) reads f(0) since 0 joined the class of w")
    (is (= [#{} 1] (flat g1 p 1)))))

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
