# cromulent

An e-graph library for Clojure, on Jolt and the JVM.

A domain-agnostic equality-saturation library in pure Clojure, one
source for Jolt and the JVM. It provides: a persistent e-graph value,
e-matching, a rewrite runner, extraction, and e-class analyses. It
does not know what `+` means.

The reference design is egg (Willsey et al., POPL 2021): deferred
rebuilding, e-class analyses, a phased runner. hegg (Haskell) shows the
same design survives purity. What is new here is (a) the persistent
value as the primary representation, with a data model shaped so
that mutable working copies can be introduced where measurement says
so, and (b) the AC work in ac-problem.md.

Working name: **cromulent**. Every e-node in an e-class is a perfectly
cromulent form of the same thing. Saturation, which grows the graph,
is `embiggen`; extraction, which pulls the best term out, may be
`yoink`. Serious aliases (`saturate`, `extract`) exist either way.

## 0. Principles

- **Performance over ergonomics, both where possible; pragmatic
  idioms.** (Captain's direction, 2026-09-13.) The public API is pure
  values in, pure values out.
- **Do not optimize everything from the start.** The design and the
  core data structures must *support* performance: dense ids so
  tables can be vectors or arrays, canonical e-nodes as hashcons keys,
  phase-separated algorithms that naturally form scopes, a seam
  between the user's term shape and the internal e-node. The v1
  *implementation* is plain persistent Clojure written with `reduce`
  and transducers. Transients and arrays go in per algorithm, where a
  `bench/` row on both runtimes points, and nowhere else.
- The user-facing term shape (tagged vectors) and the internal e-node
  representation are separate decisions. Convert at the boundary.
- One source for Jolt and the JVM; no runtime-specific fast paths
  unless a benchmark on both justifies the split.

## 1. Portability constraints and what the runtime offers

Both runtimes, one source. Verified on Jolt v0.8.7, 2026-09-13:

- Available on both: maps, vectors, sets, sorted collections, records,
  protocols, multimethods; **transients** (`transient`, `assoc!`,
  `conj!`, `persistent!`); **primitive arrays** (`long-array`, `aget`,
  `aset`, `alength`); `unchecked-*` arithmetic; `System/nanoTime`;
  exact ratios and bignums; test.check.
- Not available: Java interop, reflection, `gen-class`, `proxy`,
  `java.util`. Whether `deftype` with mutable fields works on Jolt is
  unverified and the design does not rely on it.
- `hash` values differ across runtimes; nothing may persist or compare
  hashes across processes. Structural equality is what we rely on.
- `(= 1 1.0)` is false on both; the CAS uses exact numbers only.

Measured costs, one million operations, arm64 macOS:

| operation | Jolt 0.8.7 | JVM (Clojure 1.12) |
|---|---|---|
| persistent vector `assoc` | 717 ms | 125 ms |
| transient vector `assoc!` | 420 ms | 40 ms |
| persistent hash-map `assoc`, int keys | 862 ms | 362 ms |
| transient hash-map `assoc!`, int keys | 442 ms | 192 ms |
| hash-map `get`, keys `[:+ i j]` | 701 ms | 178 ms |
| `long-array` `aset` | 12 ms | 5 ms |

Three facts inform the design below without dictating v1. Jolt is
three to six times slower than the JVM on persistent collections but
only about twice as slow on arrays. Transients roughly halve update
cost on both. Arrays are thirty-five times faster than transient
vectors on Jolt. So the data model keeps the door open to arrays and
transients; the benchmarks decide when to walk through it.

## 2. Data model

**Terms** are trees of tagged vectors. A compound node is a vector
whose first element is the operator and whose remaining elements are
child terms; anything that is not a vector is a leaf.

```clojure
[:+ [:* 2 :x] :y]        ;; (2·x) + y ; :x and :y are leaves
[:pi]                     ;; nullary operator
```

The operator can be any value with structural equality. Leaves can be
any non-vector value; a vector literal as a leaf must be wrapped by
the caller (`[:const [1 2]]`). This one shape rule keeps the core
tag-agnostic: the CAS decides the vocabulary.

**E-nodes** have the same shape with children replaced by e-class ids:
`[:+ 4 7]`, or a leaf. An e-node is *canonical* when every child id is
a union-find root. This is the *logical* e-node; the hashcons may key
on a packed form (section 5).

**E-class ids** are dense non-negative integers allocated
sequentially, which is why every id-indexed table below is a vector,
not a map.

**The persistent e-graph** is a map (or record; measure on Jolt):

```clojure
{:next-id  0
 :uf       []      ;; vector, id -> parent id; a root points to itself
 :size     []      ;; vector, root id -> class size (union by size)
 :memo     {}      ;; canonical e-node -> class id           (the hashcons)
 :classes  []      ;; vector, root id -> {:id id
                   ;;                     :nodes   #{e-node ...}
                   ;;                     :parents {e-node id ...}   ; parent e-node -> its class
                   ;;                     :data    any}             ; analysis data
                   ;;          nil for non-roots
 :by-op    {}      ;; operator -> #{root ids} whose class holds a node with that operator
 :pending  []      ;; [parent-node class-id] entries to re-key in :memo (the rebuild worklist)
 :analysis-pending []  ;; [parent-node class-id] entries whose class data must be re-made
 :dirty?   false   ;; a union has happened since the last rebuild
 :analysis nil}    ;; an Analysis value, or nil
```

A tiny `TermLike` protocol (`operator`, `children`, `make-node`,
`leaf?`) is extended to vectors by default, so the CAS or the
catalytic libraries could change representation without touching the
core. It is also the seam that lets the internal e-node form differ
from the user's. Do not build anything else generic.

## 3. Invariants

After `rebuild` (and after any scope exit), all of these hold; a
`check-invariants` function asserts them in tests after every
operation:

1. Every non-nil entry of `:classes` is at a union-find root.
2. Every key of `:memo` is canonical, and maps to a root.
3. For every class `c` and every node `n` in `(:nodes c)`,
   `(canonicalize n)` is in `:memo` and maps to `c`. (Congruence
   closure.)
4. For every class `c` and every `[p pid]` in `(:parents c)`, `p`
   mentions `c` as a child and `(find pid)` is the class containing `p`.
5. `:pending` and `:analysis-pending` are empty and `:dirty?` is false.
6. Analysis data of every class is closed under joining `make` over
   its nodes: joining what the nodes say changes nothing. For a
   lattice of finite height that is equality with the join; for
   bendix's polynomial order it is "the smallest form ever derived".
7. `:by-op` maps each operator to exactly the set of roots whose class
   holds a node with that operator. Unlike the others this one holds
   at all times, not only after rebuild: `union` moves the smaller
   class's operators to the new root as it merges.
8. (Once scoped algorithms exist.) After a scope exit, every entry of
   `:uf` points directly at its root (fully compressed).

Between `merge` and `rebuild` only 1 holds; that is the deferred
rebuilding trade and it is what makes saturation fast.

## 4. Core operations

All are pure. Operations that allocate an id return a pair.

```clojure
(egraph)                    ;; empty; (egraph {:analysis a})
(add eg term)      -> [eg' id]   ;; whole term, hashconsed bottom-up
(add-node eg node) -> [eg' id]   ;; one e-node with child ids
(find eg id)       -> root-id
(merge eg a b)     -> [eg' root] ;; union by size; queues the smaller class's parents in :pending
(rebuild eg)       -> eg'        ;; restore invariants 2..7
(class eg id)      -> class map
(nodes eg id)      -> #{canonical e-nodes of the class}
```

In v1 everything works on the persistent value directly: vector
`assoc`, map `assoc`, a read-only `find` walk, algorithms as `reduce`
over worklists. `find` is O(log n) by union by size; `rebuild` may
compress the paths it touches since it is producing a new value
anyway. The data model is shaped so that the batch algorithms
(`rebuild`, `saturate`, `ematch`, `extract`, future AC machinery) can
each later move inside a **scope** with mutable tables (section 5),
one at a time, when a benchmark says that one is the bottleneck.

**Rebuild** is egg's algorithm in its later, entry-granular form
(egg 0.9's `process_unions`): the worklists hold parent *entries*
`[parent-node class-id]`, not classes.

```
union a b
  root := the larger class (by size); queue every parent entry of the
  smaller class on pending; if the joined analysis data differs from
  either side's old data, queue that side's parents on analysis-pending
rebuild
  loop while pending or analysis-pending non-empty
    while pending non-empty
      pop [p pid]; p' := canonicalize p ; root := find pid
      if memo has p' -> other and find other ≠ root: union other root  ; queues more
      memo[p'] := root
    while analysis-pending non-empty
      pop [p pid]; root := find pid
      d := merge(data root, make(canonicalize p))
      if d ≠ data root: data root := d; queue parents(root); modify root
  one linear pass: point every id at its root, canonicalize every
  class's nodes and parents, rebuild memo from the classes
```

Why entries and not classes: the first version queued *classes* and
re-processed every parent of a queued class. When many queued classes
are merged into one big one during the same round, that big class is
repaired once per queued member. On the runner's first benchmark (the
egg README rules over 36 000 random nodes) the class of the leaf `0`,
with 7 700 parents, was repaired hundreds of times: 7.5 million
parent visits for 105 000 distinct entries, 5.1 s for one iteration
on the JVM. Entries are visited once each; with union by size an entry
is re-queued at most log n times over the life of the e-graph, so
rebuild is O(P log n) in the number of parent entries. The same
iteration now takes 0.4 s. Stale hashcons keys are left in place
until the final pass rebuilds the table; a canonical lookup can never
hit one, because a non-root id never becomes a root again.

Termination: each union strictly reduces the number of roots; each
analysis change strictly climbs a finite lattice. Same argument as egg.

## 5. Persistence and performance

The persistent value is the API and, in v1, the implementation. The
performance plan is a *path*, not a starting point:

1. v1: persistent throughout, `reduce`/transducers, no lazy seqs in
   the core algorithms (that much is idiom, not optimization).
2. `bench/` from the first milestone; the sum-of-*n* fixture and
   egg's `math` suite on both runtimes.
3. When a row shows an algorithm is the bottleneck, that algorithm
   moves inside a **scoped working copy**: same algorithm, mutable
   tables, one thread, no escape, persistent value produced at exit.
   This is `(persistent! (reduce conj! (transient v) xs))` applied to
   the e-graph, the standard Clojure answer to "pure outside, fast
   inside", and the data model below is what makes it a local change
   rather than a rewrite.

The scoped representation, when an algorithm earns it, chosen from
the measurements in section 1:

| table | persistent | scoped |
|---|---|---|
| `:uf`, `:size` | vectors | `long-array`s with path compression |
| `:memo` | hash map | transient hash map |
| `:classes` | vector | transient vector of (transient or plain) class maps |
| `:pending` | set | transient set, or a long-array used as a stack |

Scope entry copies `:uf`/`:size` into arrays (O(n), a few
milliseconds at 10⁶ ids) and calls `transient` on the maps (O(1)).
Scope exit runs one full compression pass over the array, so every
id points at its root, then `vec`s the arrays and `persistent!`s the
maps. Because exit always leaves the union-find fully compressed, the
persistent value never needs compression and single-operation `find`
stays cheap.

What the data model commits to now so that step 3 stays local:

- Ids are dense integers; every id-indexed table is a vector (later,
  an array) and never a map.
- The hashcons is keyed by canonical e-nodes; the key's internal form
  is behind the term seam, so a **packed e-node key** (operator index
  and up to two child ids in one long; larger arities fall back to
  vectors) or per-operator sub-indexes can be tried later without
  touching callers. Map lookups keyed by e-node cost about 0.7 µs on
  Jolt and will dominate e-matching; this is the first thing the
  benchmarks will point at.
- Core algorithms are written as `reduce` over explicit worklists, not
  lazy pipelines, so that swapping a persistent table for a transient
  one inside them is mechanical.
- Records vs maps for the e-graph value and class maps: undecided;
  measure on Jolt when it matters.

What persistence still buys, unchanged:

- **Timelines.** `(saturate eg rules {:timeline? true})` retains the
  e-graph after each iteration, the same idea as
  `catalytic.pure/timeline`; each retained value costs one O(n)
  union-find vector. `(diff eg1 eg2)` is a set difference on `:memo`.
- **Speculation.** Run a risky or expensive burst of rules on a copy
  (free), keep it only if extraction improves. This is approach D in
  ../design/ac-problem.md and needs no undo log.
- **Value equality** of e-graphs.

**Benchmarks from the first milestone**, in `bench/` per the
catalytic convention, timed with `System/nanoTime` on both runtimes
and with `jolt build` native binaries for headline numbers. Fixtures:
the sum-of-*n* AC blowup (../design/ac-problem.md), egg's `math` rule set and
its standard inputs, and a mixed CAS workload once bendix has one.
Every performance option above is adopted or rejected by a row in
that table, not by taste.

## 6. E-matching

Patterns are terms containing pattern variables: symbols starting with
`?`. Variables never appear in terms, so patterns are visibly distinct.

```clojure
'[:* ?a 2]
'[:+ ?x [:* ?y ?z]]
```

`cromulent.pattern`. The matcher is backtracking: candidate classes
come from `:by-op` for the pattern's operator (a leaf pattern is a
hashcons lookup; a bare variable matches every root); within a class,
each node with the operator and arity is tried, children matched
pairwise while threading a bindings map; a repeated variable must
`find` to the same root. `(ematch g p)` returns a vector of
`{:class root :bindings {?a root ...}}`; `(match-class g p id)` the
bindings for one class. `(instantiate g p bindings)` goes the other
way, returning `[g' id]`; it calls `add-node` as it walks rather than
building a term, because a term with ids at its leaves would read as
integer constants. Later, by benchmark: precompiled patterns and the
relational e-matcher (Zhang et al. 2022). Neither changes the API.

AC patterns (bag children, rest variables) are a matcher extension
specified in ../design/ac-problem.md, not part of v1.

## 7. Rewrites and the runner

A rewrite is data:

```clojure
{:name "mul-2-to-shift"
 :lhs  '[:* ?a 2]
 :rhs  '[:<< ?a 1]              ;; or (fn [eg bindings] term) for computed results
 :when (fn [eg bindings] bool)} ;; optional guard; sees analysis data
(rule "name" lhs rhs & {:keys [when]})   ;; constructor; a macro variant quotes for you
(bidirectional "name" lhs rhs)           ;; two rewrites
```

One saturation iteration, in egg's phase order so results do not
depend on rule order:

1. **search**: every rule against the same e-graph; collect matches.
2. **apply**: for each match, instantiate `:rhs` under the bindings,
   add it, union with the matched class.
3. **rebuild**.
4. **stop?** Saturated (no new node, no union); or `:iter-limit`,
   `:node-limit`, `:time-limit`.

```clojure
(embiggen eg rules {:iter-limit 30 :node-limit 10000 :time-limit-ms 5000
                    :scheduler :backoff :timeline? false})
=> {:egraph eg' :iterations n :stop-reason :saturated ; | :iter-limit | :node-limit | :time-limit
    :stats [{:iter 1 :nodes n :classes m :applied {"rule" k ...}} ...]}
```

Schedulers: `:simple` (everything, every iteration) and `:backoff`
(egg's: a rule that exceeds its match budget is banned for a doubling
number of iterations; `:match-limit` 1000 and `:ban-length` 5 by
default). A scheduler is a map `{:init :search :can-stop :report}`,
so the AC experiments can bring their own. Backoff is not our answer
to AC; it is the baseline the AC experiments (../design/ac-problem.md)
are measured against.

`:lhs` may be a *searcher* `(fn [eg] [{:class id :bindings {...}}])`
in place of a pattern, egg's `Searcher` as a function; a pattern is
the default searcher. A searcher's match may carry its own `:rhs`, a
pattern over its bindings, which takes precedence over the rule's
(then nil): one rule can say a different thing about every class.
This is what bendix's normal-form rules use (../bendix/IDEA.md
section 3). A `:check` option, `(fn [g]
problem-or-nil)`, is a dev-mode oracle: after each rule's
applications the runner rebuilds and runs it, and a problem throws
naming the rule. Any exception raised while applying a rule is
rethrown with the rule's name and the match in its data.

Decided in the implementation: a computed `:rhs` returns a pattern,
instantiated under the match's bindings, or nil to decline the match.
The guard and a computed `:rhs` see the e-graph the iteration's
search ran on, not the one being built by the other applications, so
an iteration's result is independent of rule and match order. A
match counts as applied only when its union merged two classes;
saturation is "nothing applied and the scheduler holds nothing back",
and the scheduler is only asked when nothing was applied (that is when
backoff releases a ban instead of stopping).

## 8. Extraction

```clojure
(extract eg root cost-fn) -> {:cost c :term t}
```

`cost-fn` is `(fn [e-node child-costs] number)`; the default is AST
size. Bottom-up fixpoint over all classes, egg's Extractor, costs in a
vector indexed by class id: iterate until no class's best cost
changes; a node whose child has no cost yet is skipped, which is why
cycles (`x = x + 0`) are harmless. Then rebuild the term top-down from each class's best node.
`extractor` returns a function of a class id that shares one cost
table across many extractions; `yoink` is `extract`'s alias. Ties
between equal-cost nodes go to the smaller node under
`cromulent.term/compare-nodes`, a total order that is the same on
both runtimes, so extraction is a function of the e-graph value. The cost
function must be monotone (a node costs strictly more than any child)
or a cyclic node can be chosen. bendix supplies cost functions that
encode taste (../bendix/IDEA.md); the core guarantees the minimum.

## 9. E-class analyses

Egg's mechanism, as maps of functions so analyses are data; an
e-graph carries a vector of them and every class's `:data` is a map
keyed by analysis name:

```clojure
{:name   :const-fold
 :make   (fn [eg e-node id] data)     ;; the node's data; id is the class it is (or will be) in;
                                      ;; children canonical, read them with (data eg child name)
 :merge  (fn [eg a b] data)           ;; semilattice join: associative, commutative, idempotent;
                                      ;; sees eg so it can canonicalize ids it stored
 :modify (fn [eg id] eg)              ;; may add nodes / union; may keep state under
                                      ;; [:analysis-state name] in the e-graph value
 :reconcile (fn [eg id datas] eg)}    ;; optional: the data that met in the class (the two sides
                                      ;; of a union; the old data and every node's at a recompute);
                                      ;; may add / union. bendix solves equations here.
(egraph {:analyses [a b]})            ;; run together; (data eg id :const-fold)
```

The contract that makes this work for data mentioning class ids
(bendix's polynomials name opaque classes by id): a class's data is
closed under joining `make` over its canonical nodes. `union` joins
the two sides provisionally and queues the merged class and, when
either side's data changed, that side's parents; `rebuild` then
recomputes in rounds, joining what each queued class's nodes now say
into what it had and queueing its parents when that changes. Ids in
data go stale when classes merge, so `make` and `merge` canonicalize
them through `find` and the recompute refreshes every class affected.
Termination: every recompute round strictly descends some class's
data in its analysis's order, so the join's order must be
well-founded, with no infinite descending chains. A lattice of finite
height is; bendix's total order on polynomials is because it compares
term counts, degrees and coefficient *sizes* before anything else, so
only finitely many polynomials lie below any given one. `rebuild`
asserts this with a generous round limit and throws with the
offending classes rather than spin. Tests check the invariant on
random e-graphs.
Analyses read the e-graph only through the public read API, so a later
scoped rebuild can hand them a working copy unchanged.

**Analysis-driven merging** (`:modify` unioning two classes whose data
proves them equal) is how the CAS brings decision procedures into the
e-graph (../bendix/IDEA.md, ../design/ac-problem.md approach C).
Constant folding is the degenerate case.

## 10. Testing

- `check-invariants` after every operation in tests (section 3).
- test.check generators: random terms over a small signature, random
  sequences of `add`/`merge`/`rebuild`, random rule sets. Properties:
  invariants hold; `find` is idempotent; the old value is unchanged
  after any operation (persistence); `rebuild` is idempotent.
- **Scoped and persistent agree** (once any scoped algorithm exists):
  the same operation sequence yields the same partition and memo
  either way.
- **Differential test** against a naive reference: brute-force
  congruence closure over an explicit equivalence relation on a small
  finite set of terms.
- Acceptance examples from the egg README.
- Both runtimes in CI from day one; benchmarks in `bench/` from the
  first milestone.

## 11. Later

- **Explanations**: egg's proof production. A persistent union history
  makes this easier than in egg; a CAS wants it for "show your work".
- **Relational e-matching**, **packed e-node keys**, **per-operator
  indexes**, **egglog-style Datalog rules**: all after v1, all
  API-neutral, all adopted by benchmark.

## 12. Open questions

- Pair-returning `add`/`merge` vs. an accumulator style
  (`(with-egraph eg (add! ...) (merge! ...))`). Pairs for v1. If a
  scoped tier lands, exposing it as a public `with-scope` for callers
  who add thousands of terms is a later ergonomics call.
- Should `:nodes` hold canonical or as-inserted e-nodes? egg keeps
  as-inserted and canonicalizes in repair. Decide with the invariant
  checker in hand.
- Records vs maps on Jolt (measure).

## Status

Implemented (2026-09-13), tests green on JVM (Clojure 1.12) and Jolt
v0.8.7 through both `clojure -M:test` and `jolt -M:test` / `jolt test`:

- `cromulent.term` — the representation seam (tagged vectors):
  `compound?`, `operator`, `children`, `child`, `arity`, `make`,
  `map-children`, `compare-nodes`. bendix's own vocabulary (what a
  leaf means) sits above it in `bendix.term`.
- `cromulent.core` — the persistent e-graph value: `egraph`, `add`,
  `add-node`, `lookup`, `find`, `union`, `rebuild`, `eclass`, `nodes`, `data`,
  `roots`, `class-count`, `node-count`, `canonicalize`; several
  e-class analyses per e-graph under the section 9 contract
  (`make` with the class id, `merge` with the e-graph, data maps keyed
  by name, analysis-owned state, recompute on change).
  Plain persistent Clojure throughout, as decided: no transients, no
  arrays. `rebuild` drains the parent-entry congruence worklist and
  the class-level analysis worklist of section 4 and then runs one
  linear pass that compresses every union-find path, canonicalizes
  every class's nodes and parents, and rebuilds the hashcons from the
  classes; that pass is the first thing to amortize when a benchmark
  says so.
- `cromulent.pattern` — e-matching over the operator index and
  `instantiate` (section 6).
- `cromulent.rewrite` — rules as data (`rule`, `bidirectional`) with
  pattern or searcher left-hand sides, matches that carry their own
  right-hand side, `embiggen`/`saturate` with the
  `:simple` and `:backoff` schedulers or a caller-supplied one,
  iteration/node/time limits, per-iteration stats with phase timings,
  optional timeline, the `:check` dev-mode oracle, failures that name
  the rule (section 7).
- `cromulent.extract` — `best-costs`, `extract`/`yoink`, `extractor`,
  `ast-size`, deterministic ties (section 8).
- `cromulent.check` — `violations` / `check!` over the invariants in
  section 3 (strict: after `rebuild`, memo keys, class nodes and parent
  keys are all canonical and parent ids are roots; the operator index
  is exact; analysis data equals the join over the class's nodes).
- Tests (48 tests, 170 assertions). Core: the egg README example,
  cycles, persistence, constant folding (a flat lattice nil < number <
  :conflict, so contradictory scripts join to :conflict instead of
  throwing), two analyses side by side with per-analysis joins,
  analysis state surviving in the value, and five test.check
  properties over random add/union/rebuild scripts: invariants hold
  and rebuild is idempotent; the partition equals a naive reference
  congruence closure; the same with the analysis on; the analysed
  graph merges a superset of the reference; invariants hold with two
  analyses. Matching: the egg README pattern,
  repeated variables, ground and bare-variable patterns, matching
  through a union, the index following unions before rebuild,
  instantiate reusing nodes; and three properties: soundness,
  completeness against a tree matcher, no duplicates. Rewriting: the
  egg README example under both schedulers, computed right-hand sides
  and guards, guards seeing the search snapshot whatever the rule
  order, every limit, the sum-of-5 blowup matching the formula in
  ../design/ac-problem.md (31 classes, 180 compound nodes), backoff
  banning and recovering to the same e-graph as simple, timelines, a
  custom scheduler, a searcher rule, a searcher whose matches carry
  their own right-hand sides, failures naming the rule; and
  four properties: random unsound rules over
  random scripts keep every invariant; sound integer identities
  (including two computed folding rules) preserve the value of every
  node of every class under random assignments, checked through
  extraction; a saturated e-graph is closed under its rules and
  saturates again in one quiet iteration; simple and backoff reach
  the same e-graph whenever both saturate. Extraction: smallest term,
  a cost function that prefers shifts, cycles, a shared table; and a
  property that every class's extracted term is a member of the
  class, costs its size, and is no larger than any input term there.
- `bench/` — deterministic across runtimes (identical node and class
  counts); JVM numbers include JIT warm-up; nothing is tuned:

  | fixture | n | JVM | Jolt |
  |---|---|---|---|
  | add-terms (random terms, depth ≤ 4; 35 967 distinct nodes) | 20 000 | 281 ms | 457 ms |
  | ematch `[:+ ?a [:* ?b ?c]]` on the above (4 557 matches) | | 57 ms | 68 ms |
  | ematch `[:+ ?x ?x]` on the above (32 matches) | | 17 ms | 44 ms |
  | union + rebuild (random unions on the above) | 2 000 | 114 ms | 151 ms |
  | extract, cost table for every class of the above | 35 967 | 57 ms | 131 ms |
  | embiggen, egg README rules on the above, 2 iterations (→ 45 282 nodes, 22 871 classes) | 2 | 844 ms | 2 280 ms |
  | chain-collapse (2 000-atom sum, all atoms unioned) | 2 000 | 9 ms | 27 ms |
  | ac-sum, saturate a 7-atom sum under comm + assoc (127 classes, 1 939 nodes, 8 iterations) | 7 | 96 ms | 360 ms |
  | ac-sum, the same with 8 atoms (255 classes, 6 058 nodes, 9 iterations) | 8 | 361 ms | 1 717 ms |

  The ac-sum rows are experiment 1 of ../design/ac-problem.md, the
  baseline. The embiggen row is where the class-level worklist was
  caught (section 4).

Not yet: explanations, relational e-matching, a scoped fast path; the
AC experiments beyond 1–3 live in bendix. CI workflow is written but the repository has no
remote.
