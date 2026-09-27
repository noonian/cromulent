(ns cromulent.gen
  "Generators and script runner shared by cromulent's tests and
  bendix's. It lives in src so that bendix gets it from the dependency,
  and it needs org.clojure/test.check on the classpath, which cromulent
  itself does not depend on."
  (:require [clojure.test.check.generators :as gen]
            [cromulent.core :as eg]
            [cromulent.term :as term]))

(def leaf-gen (gen/elements [:a :b :c 0 1 2]))

(defn term-gen-with
  "Random terms over :+ :* :neg with the given leaf generator."
  [leaves]
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of [(gen/tuple (gen/return :+) inner inner)
                  (gen/tuple (gen/return :*) inner inner)
                  (gen/tuple (gen/return :neg) inner)]))
   leaves))

(def term-gen (term-gen-with leaf-gen))

(def pattern-gen
  "Random patterns: terms whose leaves may also be ?x or ?y."
  (term-gen-with (gen/elements [:a :b 0 1 '?x '?y])))

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

(defn id-of
  "The root id of ground term t in a rebuilt g (adds nothing new)."
  [g t]
  (eg/find g (second (eg/add g t))))

;; ---------------------------------------------------------------------------
;; for the runner and extraction tests

(def terms-gen
  "A handful of random terms to add: an add-only script, so no
  contradictory equalities are asserted."
  (gen/vector term-gen 1 12))

(defn add-terms
  "Add every term of ts to g. Returns {:egraph g :terms #{...}} rebuilt."
  [g ts]
  {:egraph (eg/rebuild (reduce (fn [g t] (first (eg/add g t))) g ts))
   :terms (into #{} (mapcat subterms) ts)})

(def rule-gen
  "A random rewrite: a random pattern lhs and an rhs whose variables
  are drawn from the lhs, so the rule is well-formed. Not sound."
  (gen/bind pattern-gen
            (fn [lhs]
              (let [vs (into #{} (filter symbol?) (subterms lhs))]
                (gen/fmap (fn [rhs] {:lhs lhs :rhs rhs})
                          (term-gen-with (gen/elements (into [:a :b 0 1] vs))))))))

(def rules-gen
  "One to four random rules with distinct names."
  (gen/fmap (fn [rs] (vec (map-indexed (fn [i r] (assoc r :name (str "r" i))) rs)))
            (gen/vector rule-gen 1 4)))

(defn evaluate
  "The integer value of ground term t under env, a map of keyword -> number."
  [t env]
  (cond
    (term/compound? t)
    (let [vs (map #(evaluate % env) (term/children t))]
      (case (term/operator t)
        :+ (reduce + vs)
        :* (reduce * vs)
        :neg (- (first vs))))
    (keyword? t) (get env t)
    :else t))

(defn size
  "Number of nodes in term t."
  [t]
  (count (subterms t)))
