(ns cromulent.gen
  "Generators and script runner shared by the test namespaces."
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
