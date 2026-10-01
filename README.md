# cromulent

A persistent e-graph for Clojure, running on [Jolt](https://github.com/jolt-lang/jolt),
the JVM and ClojureScript from one source. The data structure of equality
saturation, as a value: every operation returns a new e-graph and
leaves the old one intact.

**Status: a toy.** cromulent is a vehicle for learning and
experimentation, built largely with an LLM. Nothing about its API or
performance is promised; do not build on it. If you want an e-graph in
Clojure for real work, look first at
[ansatz](https://github.com/replikativ/ansatz), whose `grind` tactic
ships a persistent e-graph with congruence closure and e-matching
inside a Lean-4-style verified programming library, and at
[egg](https://egraphs-good.github.io/) for the reference
implementation of the ideas this one follows.

```clojure
(require '[cromulent.core :as eg])

(let [g (eg/egraph)
      [g m]  (eg/add g [:* :a 2])            ; terms are tagged vectors
      [g s]  (eg/add g [:<< :a 1])
      [g dm] (eg/add g [:/ [:* :a 2] 2])
      [g ds] (eg/add g [:/ [:<< :a 1] 2])
      [g _]  (eg/union g m s)                ; assert a*2 = a<<1
      g      (eg/rebuild g)]                 ; restore congruence closure
  (= (eg/find g dm) (eg/find g ds)))         ; => true: (a*2)/2 = (a<<1)/2
```

`add` shares every subterm already present. `union` is deferred:
call `rebuild` before relying on congruence or the hashcons. `nodes`
returns the canonical e-nodes of a class; `eclass` the class map.

**Patterns** are terms with `?variables`; matching finds every class
and binding where one occurs, and `instantiate` builds the other side:

```clojure
(require '[cromulent.pattern :as pat])

(pat/ematch g '[:* ?a 2])
;; => [{:class 2 :bindings {?a 0}}]        ; ids are e-class ids
(pat/instantiate g '[:<< ?a 1] {'?a 0})
;; => [g' 3]                              ; the class of a<<1, added if missing
```

**Rewrites** are data, and `embiggen` (alias `saturate`) runs them to
a fixpoint or a limit; `extract` (alias `yoink`) then pulls the
cheapest term out of a class:

```clojure
(require '[cromulent.rewrite :as rw] '[cromulent.extract :as ex])

(defn constant-in [g id] (some #(when (number? %) %) (eg/nodes g id)))

(def rules [(rw/rule "commute-add" '[:+ ?a ?b] '[:+ ?b ?a])
            (rw/rule "commute-mul" '[:* ?a ?b] '[:* ?b ?a])
            (rw/rule "add-0"       '[:+ ?a 0]  '?a)
            (rw/rule "mul-1"       '[:* ?a 1]  '?a)
            (rw/rule "fold"        '[:+ ?a ?b]                    ; a computed right-hand side:
                     (fn [g {:syms [?a ?b]}]                      ; a pattern, or nil to decline
                       (let [x (constant-in g ?a), y (constant-in g ?b)]
                         (when (and x y) (+ x y)))))
            (rw/rule "div-self"    '[:/ ?a ?a] 1
                     :when (fn [g {:syms [?a]}] (not= 0 (constant-in g ?a))))])

(let [[g r] (eg/add (eg/egraph) [:+ 0 [:* 1 :a]])
      {:keys [egraph stop-reason iterations stats]} (rw/embiggen g rules {:iter-limit 30 :node-limit 10000})]
  [stop-reason iterations (ex/extract egraph r)])
;; => [:saturated 3 {:cost 1 :term :a}]
```

Each iteration searches every rule against the same e-graph, applies
every match, then rebuilds, so the result does not depend on rule
order. Guards and computed right-hand sides see the e-graph the
search ran on. The default scheduler is egg's backoff (`:scheduler
:simple` applies everything, every iteration); `:stats` has per-rule
match and application counts and phase timings for every iteration,
and `:timeline? true` keeps every intermediate e-graph. Cost
functions are `(fn [e-node child-costs] number)`; `ex/extractor`
shares one cost table across many extractions.

An **e-class analysis** attaches lattice data to every class and may
merge classes it proves equal; several run side by side, each under
its own name:

```clojure
(eg/egraph {:analyses [{:name   :const-fold
                        :make   (fn [g node id] ...)   ; data for a node in class id, from
                                                       ; its children's (eg/data g child :const-fold)
                        :merge  (fn [g a b] ...)       ; semilattice join
                        :modify (fn [g id] ...)        ; optional; may add nodes and union
                        :reconcile (fn [g id datas] ...)}]}) ; optional; sees the data that met
```

A class's data is always the join of `make` over its nodes; `rebuild`
recomputes whatever a union or a child's change affected.

See `test/cromulent/core_test.clj` for a complete constant-folding
analysis, and `cromulent.check/violations` for the invariants a
rebuilt e-graph satisfies.

## Running

```
clojure -M:test     jolt -M:test     jolt test      # the suite, either runtime
clojure -M:bench    jolt -M:bench                   # throughput fixtures
cd ../orrery && npm run smoke:local                 # the same facts on node
```

## Portability

The library is `.cljc` and compiles unchanged for ClojureScript
([orrery](https://github.com/noonian/orrery), the explorer, builds it
with shadow-cljs). `cromulent.platform` is the one file that knows the
runtime, the clock; the two `catch` clauses in `cromulent.rewrite` are
the only other reader conditionals. The hashcons key is `op·2^42 +
a·2^21 + b`, under 2^53 so that it is exact in a JavaScript double as
well as a fixnum on Chez and a long on the JVM; an e-graph therefore
holds at most 2 048 operators and 2 097 150 class ids, and either
overflow throws. `cromulent.smoke` (under `src/`) is a vector of
runtime-stable facts about fixed runs, asserted by the suite on the
JVM and Jolt and by orrery's node build on ClojureScript: class and
node counts, iterations, stop reasons, per-rule counts and costs are
identical on the three runtimes. Root ids and tied extractions are
not: hash iteration order differs per runtime, so a term is asserted
across runtimes only when its cost is a unique minimum. The test
suites and the bench stay JVM and Jolt.

[IDEA.md](IDEA.md) is the design and status.
