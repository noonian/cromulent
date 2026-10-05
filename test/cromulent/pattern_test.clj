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

(defn- flat-seq
  "[matches found] of p in g as `ematch-flat` gives them: the matches
  it wrote, each [class binding ...], in the order it wrote them, and
  how many it found."
  [g p since]
  (let [[^longs buf n found] (pat/ematch-flat g p (long-array 4) since)
        stride (inc (count (:vars (pat/compile p))))]
    [(vec (for [m (range n)] (mapv #(aget buf (+ (* m stride) %)) (range stride)))) found]))

(defn- flat
  "`flat-seq` with the matches as a set."
  [g p since]
  (update (flat-seq g p since) 0 set))

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

(deftest freshness-comes-from-any-child
  ;; f(g(x), h(y)) of epoch 0. In epoch 1 a new g(x2) joins the class
  ;; of g(x) and a new h(y2) that of h(y); the new nodes are the ones
  ;; that move, so f, g(x) and h(y) keep their stamps. Of the four
  ;; matches now, only the old one has no fresh node.
  (let [p '[:f [:g ?a] [:h ?b]]
        [g fgh] (eg/add (eg/egraph) [:f [:g :x] [:h :y]])
        {x :x, y :y, gx [:g :x], hy [:h :y]} (ids g :x :y [:g :x] [:h :y])
        [g1 gx2] (eg/add (eg/next-epoch g) [:g :x2])
        [g1 hy2] (eg/add g1 [:h :y2])
        g1 (eg/rebuild (first (eg/union (first (eg/union g1 gx gx2)) hy hy2)))
        {x2 :x2, y2 :y2} (ids g1 :x2 :y2)
        f (eg/find g1 fgh)]
    (is (empty? (check/violations g1)))
    (is (= [#{[f x y]} 1] (flat g p nil)))
    (is (= [#{[f x2 y] [f x y2] [f x2 y2]} 4] (flat g1 p 0)))
    (is (= [#{} 4] (flat g1 p 1)))
    (is (= 4 (count (first (flat g1 p nil)))))))

(deftest the-buffer-grows-to-fit
  ;; one match is wider than the buffer handed in, even doubled
  (let [p '[:f ?a ?b ?c ?d ?e ?f ?g ?h]
        [g f] (eg/add (eg/egraph) [:f 1 2 3 4 5 6 7 8])
        [buf n found] (pat/ematch-flat g p (long-array 4))]
    (is (= [1 1] [n found]))
    (is (= (into [f] (map #(cg/id-of g %)) (range 1 9)) (vec (take 9 buf))))))

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

(defn- fresh-match?
  "Has the match of pattern p under bindings a node stamped after
  since? The reference for `ematch-flat`: the match's nodes are found
  from the bindings by lookup, from the leaves of the pattern up."
  [g p bindings since]
  (letfn [(fresh? [nid] (> (nth (:stamps g) nid) since))
          (walk [p]                                ; [class fresh?]
            (cond
              (pat/variable? p)
              [(get bindings p) false]

              (term/compound? p)
              (let [cs (mapv walk (term/children p))
                    nid (eg/node-id g (term/make (term/operator p) (mapv first cs)))]
                [(eg/find g nid) (boolean (or (some second cs) (fresh? nid)))])

              :else
              (let [nid (eg/node-id g p)]
                [(eg/find g nid) (fresh? nid)])))]
    (second (walk p))))

(defn- shape
  "The top `depth` levels of ground term t as a pattern: whatever lies
  below them and every keyword leaf a variable, the numbers kept. With
  share?, equal subterms get the same variable, so a variable may well
  repeat; without, every variable is new."
  [t depth share?]
  (let [names (atom {}), n (atom 0)
        variable (fn [t]
                   (or (when share? (get @names t))
                       (let [v (symbol (str "?k" (swap! n inc)))]
                         (swap! names assoc t v)
                         v)))]
    (letfn [(go [t d]
              (cond
                (and (term/compound? t) (pos? d))
                (term/make (term/operator t) (mapv #(go % (dec d)) (term/children t)))

                (number? t) t
                :else (variable t)))]
      (go t depth))))

(deftest only-the-fresh-matches-are-written
  ;; a script, then an epoch, then another script. A search since that
  ;; epoch writes exactly the matches that have a node stamped after
  ;; it, in the order `ematch` finds them, and counts them all. The
  ;; patterns each time: a random one, and the shape of one of the
  ;; larger terms of the scripts to four depths, which is sure to
  ;; match, and at the shallower depths in many ways, each both with
  ;; a variable of its own for every subterm and with equal subterms
  ;; sharing one. So both ways of searching are tried, one operator
  ;; and deeper, with and without a repeated variable.
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [before cg/script-gen, after cg/script-gen, p cg/pattern-gen, i gen/nat]
               (let [{g0 :egraph, ts0 :terms} (cg/run-script (eg/egraph) before)
                     since (:epoch g0)
                     {g :egraph, ts :terms} (cg/run-script (eg/next-epoch g0) after)
                     larger (->> (into ts0 ts) (filter term/compound?) (sort-by (juxt (comp - cg/size) pr-str)))
                     t (when (seq larger) (nth larger (mod i (inc (quot (count larger) 3)))))]
                 (every? (fn [p]
                           (or (not (term/compound? p))
                               (let [vars (:vars (pat/compile p))
                                     all (pat/ematch g p)
                                     row (fn [{:keys [class bindings]}] (into [class] (map bindings) vars))]
                                 (and (= [(mapv row all) (count all)] (flat-seq g p nil))
                                      (= [(into [] (comp (filter #(fresh-match? g p (:bindings %) since)) (map row)) all)
                                          (count all)]
                                         (flat-seq g p since))
                                      (= [[] (count all)] (flat-seq g p (:epoch g)))))))
                         (cond-> [p]
                           t (into (for [depth [1 2 3 9], share? [false true]] (shape t depth share?))))))))]
    (is (:pass? res) (pr-str res))))

(deftest ematch-has-no-duplicates
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops cg/script-gen, p cg/pattern-gen]
               (let [ms (pat/ematch (:egraph (cg/run-script (eg/egraph) ops)) p)]
                 (= (count ms) (count (set ms))))))]
    (is (:pass? res) (pr-str res))))
