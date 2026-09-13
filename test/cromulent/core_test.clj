(ns cromulent.core-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [cromulent.core :as eg]
            [cromulent.check :as check]
            [cromulent.term :as term]))

(defn- ok?
  "Assert g is well-formed; returns g."
  [g]
  (let [vs (check/violations g)]
    (is (empty? vs) (pr-str vs))
    g))

;; ---------------------------------------------------------------------------
;; examples

(deftest add-is-hashconsed
  (let [g (eg/egraph)
        [g a] (eg/add g [:+ :x :y])
        [g b] (eg/add g [:+ :x :y])
        [g c] (eg/add g [:+ :y :x])]
    (is (= a b) "the same term twice is one class")
    (is (not= a c) "structurally different terms are different classes")
    (is (= 4 (eg/class-count g)) ":x :y [:+ x y] [:+ y x]")
    (is (= 4 (eg/node-count g)))
    (is (= #{[:+ (eg/find g (second (eg/add g :x))) (eg/find g (second (eg/add g :y)))]}
           (eg/nodes g a)))
    (ok? g)))

(deftest union-and-congruence
  ;; egg's README example: a*2 = a<<1, so (a*2)/2 = (a<<1)/2 by congruence
  (let [g (eg/egraph)
        [g m]  (eg/add g [:* :a 2])
        [g s]  (eg/add g [:<< :a 1])
        [g dm] (eg/add g [:/ [:* :a 2] 2])
        [g ds] (eg/add g [:/ [:<< :a 1] 2])]
    (is (not= (eg/find g dm) (eg/find g ds)))
    (let [[g _] (eg/union g m s)
          g (eg/rebuild g)]
      (ok? g)
      (is (= (eg/find g m) (eg/find g s)))
      (is (= (eg/find g dm) (eg/find g ds)) "equal children give equal parents")
      (is (= 1 (count (eg/nodes g dm))) "the two division nodes are congruent, so one canonical node")
      (is (= 2 (count (eg/nodes g m))))
      (is (= 5 (eg/class-count g)) ":a 2 1 {a*2, a<<1} {(a*2)/2, (a<<1)/2}"))))

(deftest cycles-terminate
  (let [g (eg/egraph)
        [g x]  (eg/add g :x)
        [g x0] (eg/add g [:+ :x 0])
        [g _]  (eg/union g x x0)
        g (eg/rebuild g)
        [g zero] (eg/add g 0)]
    (ok? g)
    (is (= (eg/find g x) (eg/find g x0)))
    (is (contains? (eg/nodes g x) [:+ (eg/find g x) zero]) "the class contains itself as a child")
    (is (= g (eg/rebuild g)) "rebuild is idempotent")))

(deftest persistence
  (let [g0 (eg/egraph)
        [g1 _] (eg/add g0 [:+ :x :y])
        [g2 _] (eg/add g1 [:* :x :y])]
    (is (= (eg/egraph) g0) "the empty e-graph is unchanged")
    (is (= 3 (eg/class-count g1)))
    (is (= 4 (eg/class-count g2)))
    (is (= g1 (first (eg/add g0 [:+ :x :y]))) "same operations, same value")))

;; ---------------------------------------------------------------------------
;; a constant-folding analysis, the canonical e-class analysis
;;
;; The data is a flat lattice: nil (unknown) < number < :conflict. Two
;; different constants in one class join to :conflict rather than
;; throwing, because random scripts assert contradictions on purpose;
;; a CAS would treat :conflict as "a rule is unsound".

(def const-fold
  {:name :const-fold
   :make (fn [g node]
           (if (term/compound? node)
             (let [ds (map #(:data (eg/eclass g %)) (term/children node))]
               (cond
                 (some #{:conflict} ds) :conflict
                 (every? number? ds) (case (term/operator node)
                                       :+ (reduce + ds)
                                       :* (reduce * ds)
                                       :neg (- (first ds))
                                       nil)
                 :else nil))
             (when (number? node) node)))
   :merge (fn [a b]
            (cond
              (nil? a) b
              (nil? b) a
              (= a b) a
              :else :conflict))
   :modify (fn [g id]
             (let [d (:data (eg/eclass g id))]
               (if (number? d)
                 (let [[g cid] (eg/add g d)]
                   (first (eg/union g id cid)))
                 g)))})

(deftest constant-conflict-is-a-lattice-top
  (let [g (eg/egraph {:analysis const-fold})
        [g zero] (eg/add g 0)
        [g one]  (eg/add g 1)
        [g s]    (eg/add g [:+ 0 :x])
        [g _]    (eg/union g zero one)
        g (eg/rebuild g)]
    (ok? g)
    (is (= :conflict (:data (eg/eclass g zero))))
    (is (= :conflict (:data (eg/eclass g s))) "conflict propagates to parents")))

(deftest constant-folding
  (let [g (eg/egraph {:analysis const-fold})
        [g r] (eg/add g [:+ 1 [:* 2 3]])
        g (eg/rebuild g)
        [g seven] (eg/add g 7)]
    (ok? g)
    (is (= (eg/find g r) (eg/find g seven)) "1 + 2*3 lands in the class of 7")
    (is (= 7 (:data (eg/eclass g r))))))

(deftest constant-folding-through-union
  ;; x*2 is added first; only later is x asserted equal to 3
  (let [g (eg/egraph {:analysis const-fold})
        [g x2] (eg/add g [:* :x 2])
        [g x]  (eg/add g :x)
        [g three] (eg/add g 3)
        [g _] (eg/union g x three)
        g (eg/rebuild g)
        [g six] (eg/add g 6)]
    (ok? g)
    (is (= 3 (:data (eg/eclass g x))))
    (is (= 6 (:data (eg/eclass g x2))))
    (is (= (eg/find g x2) (eg/find g six)) "the parent folds once its child is known")))

;; ---------------------------------------------------------------------------
;; property tests

(def leaf-gen (gen/elements [:a :b :c 0 1 2]))

(def term-gen
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/tuple (gen/return :+) inner inner)
                  (gen/tuple (gen/return :*) inner inner)
                  (gen/tuple (gen/return :neg) inner)]))
   leaf-gen))

(def op-gen
  (gen/frequency [[5 (gen/tuple (gen/return :add) term-gen)]
                  [3 (gen/tuple (gen/return :union) term-gen term-gen)]
                  [1 (gen/return [:rebuild])]]))

(def script-gen (gen/vector op-gen 1 40))

(defn subterms [t]
  (if (term/compound? t)
    (cons t (mapcat subterms (term/children t)))
    [t]))

(defn run-script
  "Run a script of [:add t] / [:union t1 t2] / [:rebuild] ops against g.
  Returns {:egraph g :terms #{...} :eqs [[t1 t2] ...]} with g rebuilt."
  [g ops]
  (-> (reduce (fn [{:keys [egraph terms eqs]} [op & args]]
                (case op
                  :add (let [[t] args
                             [g _] (eg/add egraph t)]
                         {:egraph g :terms (into terms (subterms t)) :eqs eqs})
                  :union (let [[t1 t2] args
                               [g a] (eg/add egraph t1)
                               [g b] (eg/add g t2)
                               [g _] (eg/union g a b)]
                           {:egraph g
                            :terms (into terms (concat (subterms t1) (subterms t2)))
                            :eqs (conj eqs [t1 t2])})
                  :rebuild {:egraph (eg/rebuild egraph) :terms terms :eqs eqs}))
              {:egraph g :terms #{} :eqs []}
              ops)
      (update :egraph eg/rebuild)))

;; A naive reference: congruence closure over a finite set of ground
;; terms (closed under subterms), as a map term -> parent term.

(defn- rep-find [rep t]
  (let [p (rep t)]
    (if (= p t) t (recur rep p))))

(defn- rep-union [rep a b]
  (let [ra (rep-find rep a), rb (rep-find rep b)]
    (if (= ra rb) rep (assoc rep ra rb))))

(defn reference-closure [terms eqs]
  (let [rep0 (reduce (fn [rep [a b]] (rep-union rep a b))
                     (into {} (map (fn [t] [t t])) terms)
                     eqs)
        compounds (vec (filter term/compound? terms))
        congruent? (fn [rep s t]
                     (and (= (term/operator s) (term/operator t))
                          (= (term/arity s) (term/arity t))
                          (every? true? (map #(= (rep-find rep %1) (rep-find rep %2))
                                             (term/children s) (term/children t)))))]
    (loop [rep rep0]
      (let [rep' (reduce (fn [rep [s t]] (if (congruent? rep s t) (rep-union rep s t) rep))
                         rep
                         (for [s compounds, t compounds :when (not= s t)] [s t]))]
        (if (= rep' rep) rep (recur rep'))))))

(defn same-partition?
  "Do g and the reference closure agree on every pair of terms?"
  [g terms rep]
  (let [id-of (fn [t] (eg/find g (second (eg/add g t))))]
    (every? (fn [[s t]]
              (= (= (rep-find rep s) (rep-find rep t))
                 (= (id-of s) (id-of t))))
            (for [s terms, t terms] [s t]))))

(def ^:private num-tests 200)

(deftest invariants-hold-for-random-scripts
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops script-gen]
               (let [g (:egraph (run-script (eg/egraph) ops))]
                 (and (empty? (check/violations g))
                      (= g (eg/rebuild g))))))]
    (is (:pass? res) (pr-str res))))

(deftest matches-reference-congruence-closure
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops script-gen]
               (let [{:keys [egraph terms eqs]} (run-script (eg/egraph) ops)]
                 (same-partition? egraph terms (reference-closure terms eqs)))))]
    (is (:pass? res) (pr-str res))))

(deftest invariants-hold-with-analysis
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops script-gen]
               (let [g (:egraph (run-script (eg/egraph {:analysis const-fold}) ops))]
                 (and (empty? (check/violations g))
                      (= g (eg/rebuild g))))))]
    (is (:pass? res) (pr-str res))))

(deftest analysis-only-merges-more
  ;; every equality the reference derives, the analysed graph also has
  (let [res (tc/quick-check
             num-tests
             (prop/for-all [ops script-gen]
               (let [{:keys [egraph terms eqs]} (run-script (eg/egraph {:analysis const-fold}) ops)
                     rep (reference-closure terms eqs)
                     id-of (fn [t] (eg/find egraph (second (eg/add egraph t))))]
                 (every? (fn [[s t]]
                           (or (not= (rep-find rep s) (rep-find rep t))
                               (= (id-of s) (id-of t))))
                         (for [s terms, t terms] [s t])))))]
    (is (:pass? res) (pr-str res))))
