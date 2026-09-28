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
  idioms.** (Decided 2026-09-13.) The public API is pure
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
- One source for Jolt, the JVM and ClojureScript; no runtime-specific
  fast paths unless a benchmark on both primary runtimes justifies the
  split.

## 1. Portability constraints and what the runtime offers

Both primary runtimes, one source. Verified on Jolt v0.8.7, 2026-09-13:

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

The third runtime, ClojureScript (2026-09-25, for orrery): the source
is `.cljc` and compiles unchanged under shadow-cljs. `long-array`,
`aset`, `aget` and `long` exist in ClojureScript core (a JS array; the
`^longs` hints are ignored). What differs: a number is exact only to
2^53, so the packed key was narrowed (section 5, decision 2); a shift
is 32-bit, so backoff doubles by multiplication; there is no
exception class, so the runner's two `catch` clauses are
`#?(:clj Exception :default :default)`; and the clock is
`cromulent.platform/now-ms`, the one file with reader conditionals,
as `catalytic.defaults` is for catalytic-buffer. Hash iteration order
differs there too, so root ids and tied extractions are stable per
runtime only (section 8). No ratio or bignum exists; that is bendix's
problem, not this library's.

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
 :memo     {}      ;; packed key -> class id: the hashcons for compound nodes of
                   ;; arity ≤ 2, keyed by op-index·2^48 + a·2^24 + b (section 5)
 :memo-other {}    ;; canonical e-node -> class id for leaves and arity ≥ 3
 :ops      {}      ;; operator -> index; :op-names is the inverse vector
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

The persistent value is the API and, in v1, the implementation. Every
performance option is adopted or rejected by a row in `bench/` on
both runtimes, and Jolt is the primary target (the author's own
runtime, 2026-09-25): a change must pay on Jolt. Nothing earlier in
this section is canon. It is re-derived from measurement each time a
row points here, and it was on 2026-09-25, when the plan that stood
before (arrays and a scoped working copy) did not survive Jolt's
numbers.

### Measured: the AC-10 yardstick (2026-09-25)

Philip Zucker's Lambda MicroEgg post (philipzucker.com/lambda_miller_egg,
2026-09-20) saturates a ten-atom sum under commutativity and one
associativity rule and reports, on his machine, egg at about 0.6 s
and his Rust at 1.5 s, with per-phase times. The same run here
(`bench/` `ac-sum` at 10: 1 023 classes and 57 012 nodes, exactly the
formula of ../design/ac-problem.md section 1, which his counts
confirm to the node; 3.34 million matches over ten iterations, 136
thousand of them applied):

| phase | JVM (Clojure 1.12) | Jolt 0.8.12 | lambda-microegg |
|---|---|---|---|
| search | 2 658 ms | 8 600 ms | 350 ms |
| apply | 4 278 ms | 11 861 ms | 1 000 ms |
| rebuild | 633 ms | 1 039 ms | 152 ms |
| total | 7 595 ms | 21 543 ms | about 1 500 ms |

Two facts located the cost in this run. Search writes nothing and was
the worst phase by ratio; rebuild, where every persistent write
happens, was the best.
Iterations 9 and 10 change nothing, the graph being saturated, and
cost 3.4 s of the 7.6 on the JVM and 10.3 s of the 21.5 on Jolt. A
sampling profile of the JVM run, self time by the nearest function of
ours: the union-find lookup 26%, the matcher 32%, the hashcons path
(`add-node`, `instantiate`, node construction) 33%, rebuild with
union and merge 7%; frames that write a persistent structure are
about 3% of samples. The union-find lookup was called 40.1 million
times with a mean of 0.05 hops and a longest chain of 3, so its cost
is the constant per call and not the chains. Immutability is not the
cost. The cost is the per-operation constant of building and hashing
a fresh vector key at every hashcons lookup, and an interpreted,
seq-based matcher; a mutable Clojure written the same way would keep
both.

The later passes below reversed the ranking. In the 2026-09-27 run
("Measured: Jolt 0.8.13"), search is 1.6 times lambda-microegg's on
the JVM, and rebuild is the furthest phase on both runtimes, 4.2 and
6.5 times. No profile of rebuild has been taken since, so whether
the persistent writes explain that gap is an open question.

### Measured: the primitives (2026-09-25)

Nanoseconds per operation, loop overhead subtracted, best of five, on
this machine (arm64 macOS). The scripts were scratch work; the
numbers are the record, and they are the rows the decisions below
rest on.

| operation | JVM | Jolt 0.8.12 |
|---|---|---|
| `nth` on a 3-vector | 1.1 | 6.3 |
| `get` on a 3-vector | 6.0 | 10.3 |
| a 3-vector invoked as a function | 1.6 | 11.4 |
| `nth` on a 152 003-vector | 9.6 | 20.2 |
| `aget` on a `long-array` | 2.1 | 15.0 |
| `hash` of a fixnum | 5.0 | 29.2 |
| `hash` of a keyword | 3.4 | 10.9 |
| `hash` of a vector hashed before | 5.3 | 14.0 |
| `hash` of a fresh 3-vector | 17.9 | 212.7 |
| `=` on two equal 3-vectors | 9.6 | 34.5 to 49.9 |
| `=` on two fixnums | 0.0 | 1.2 |
| `==` on two fixnums | 0.0 | 34.2 |
| `+`, `*`, `bit-and`, `<` on fixnums | 0.1 to 0.3 | 0.7 to 1.4 |
| `bit-shift-left` | 0.1 | 16.3 |
| `bit-or` of a shift and a fixnum | 0.1 | 34.9 |
| pack three fields by multiplication and addition | 0.5 | 1.7 |
| `get` on a 2-entry map, keyword key | 5.1 | 6.9 |
| `get` on a 3-entry map, symbol key | 15.5 | 22.2 |
| `assoc` onto a 3-entry map | 30.7 | 54.8 |
| `contains?` on a 500-set of vectors, key hashed before | 30.9 | 70.2 |
| the same with a fresh key | 57.5 | 182.6 |
| hashcons `get`, 57 000 entries, vector key hashed before | 39.4 | 92.0 |
| the same, vector key built fresh | 107.9 | 422.9 |
| the same, fixnum key | 39.3 | 156.1 |
| the same, fixnum key packed on the spot | 74.2 | 198.6 |
| `sorted-map` `get`, fixnum key, 57 000 entries | 156.4 | 737.9 |
| array open-addressing table `get`, fixnum key, 1.4 mean probes | 36.8 | 212.1 |
| hashcons `assoc`, vector key | 149.0 | 590.4 |
| hashcons `assoc`, fixnum key | 119.3 | 458.2 |
| walk a 3-vector with `first` and `rest` | | 119.0 |
| walk a 3-vector by index | | 62.3 |
| `reduce` over a 500-set, per element | | 22.0 |
| `reduce` over a 500-vector, per element | | 6.7 |
| `into []` with `mapcat`, per element | | 138.9 |
| `loop` with `conj!`, per element | | 55.6 |
| bind two pattern variables into a map | | 67.1 |
| `variable?` by parsing the symbol's name | | 47.5 |
| union-find `find` as written, mean 0.05 hops | 16.3 | 37.0 |
| the same over a `long-array` with `==` | 2.8 | 47.9 |

The three "built fresh" and "packed on the spot" hashcons rows
include three `nth` reads of the ids from 57 000-vectors, about 40 ns
on Jolt, the same in each.

What this says about Jolt, which is where it matters: arithmetic,
`=` on fixnums and keywords, `nth` and `count` are cheap; hashing a
fixnum, a shift, `==` and `=` on a vector each cost tens of
nanoseconds; hashing a fresh vector costs two hundred; a persistent
map read costs a hundred to a hundred and sixty with a fixnum key and
four hundred with a fresh vector key; and an array read costs what a
vector read does, so arrays buy nothing on reads and pay only on
writes (`aset` 12 ns against `assoc` 700 in section 1). The JVM has
the same shape at a tenth to a fortieth of the constants, except that
a fresh vector key costs it too.

Rules for hot code in this codebase, both runtimes, each a row above:
`nth` and never `get` on a vector; index loops and never `first` and
`rest`; `reduce`, or `loop` with `conj!`, and never `into` with a
transducer, per element; multiply and never shift, to pack (and a
shift is 32-bit in JavaScript); `=` and never `==` on ids; never
build and hash a fresh vector in a hot path; resolve a pattern's
symbols once and never per visit.

### Decisions (2026-09-25; built the same day)

1. **Compiled patterns** (section 6). A scratch prototype, index loops
   over node children, variables as registers in a `long-array` restored
   on backtrack, no `find` on the children of a rebuilt graph, a
   callback per match, found the same 204 630 matches of the
   associativity pattern on the saturated AC-9 graph in 35.9 ms
   against 148.9 as written on the JVM, and in 121.6 against 508.7 on
   Jolt: 4.1× and 4.2×.
2. **Packed hashcons keys.** The memo is keyed by a fixnum for a
   compound node of arity two or less: `op·2^42 + a·2^21 + b`, by
   multiplication and addition, since shifts cost 16 to 35 ns on
   Jolt; an absent child is written as 2^21 − 1; the sum stays under
   2^53, a fixnum on Chez, a long on the JVM and exact in a JavaScript
   double, so one layout serves all three runtimes (narrowed from
   2^48/2^24 on 2026-09-25 for the ClojureScript port; the old layout
   collided silently in a double from the 33rd operator). Operators
   are interned per e-graph in `:ops` (operator to index) and
   `:op-names` (index to operator), assigned on first `add-node`; ids
   are bounded at 2^21 − 2 (2 097 150; the AC-10 run allocates about
   sixty thousand, AC-13 would be the first to overflow) and
   operators at 2^11 (2 048; bendix uses about fifteen), and either
   overflow throws. **Measured, the key layout** (2026-09-25, three
   runs each, medians; the change is two multiplication constants):
   JVM ac-sum 10 3 374 → 3 352 ms, ac-sum 8 179 → 178, egg rules
   851 → 815, add-terms 224 → 224, union+rebuild 113 → 109; Jolt
   ac-sum 10 7 212 → 7 068, ac-sum 8 420 → 417, egg rules 1 331 →
   1 314, add-terms 344 → 339, union+rebuild 152 → 139. Every row
   within noise or faster on both, so there is one layout and no
   per-platform constant. Leaves and nodes of arity three or more keep the node
   itself as the key, in a second map `:memo-other`, because a leaf
   number would collide with a packed key; `node-count` sums the two.
   E-nodes stay tagged vectors everywhere else, in `:nodes`,
   `:parents`, matching, extraction and analyses: a stored node
   carries its hash on both runtimes (14 ns to re-hash on Jolt), so
   sets and maps over stored nodes are cheap, and only the lookup of
   a *fresh* node pays, which is what the packed key removes: about
   380 to 160 ns per lookup on Jolt and 108 to 40 on the JVM, the
   shared index overhead aside. Keys are built at `add-node` and
   `lookup` (canonical children, then the key), in `process-pending`
   when a parent is re-keyed, in `compress-and-canonicalize` when the
   memo is rebuilt, for a ground sub-pattern at the start of a
   search, and in the compiled `instantiate`, which computes the key
   from the operator index and the registers without building the node
   vector unless the node is new.
3. **No union-find lookup on children during search when the graph
   is clean.** After `rebuild` every stored node is canonical
   (invariant 3) and the runner searches rebuilt graphs only, so the
   compiled matcher takes child ids as they are when `:dirty?` is
   false and calls `find` otherwise. Public `ematch` on a graph with
   unions pending keeps its meaning, and the tests for matching
   through a union before rebuild stand. This removes about half of
   the 40 million lookups.
4. **Hot loops read `:uf` once.** `find` pays a keyword lookup on the
   e-graph map before the vector read; the matcher and `instantiate`
   fetch the vector once per phase and use a `find-in` over it.
5. **`instantiate` compiled with the pattern.** The right-hand side
   compiles to a plan; per compound node it builds the node from the
   bound ids and calls `add-node`, whose hit path is canonicalize,
   pack, one map read and a `find`, allocating nothing but the node
   vector. Matches keep one representation, `{:class :bindings}` maps,
   for the public API, searchers, guards and computed right-hand
   sides alike; the map costs about 165 ns per match on Jolt (three
   bindings), a tenth of a match's search, and a second register-based
   representation was not worth a second contract.

**Measured when built** (2026-09-25), the same run as above:

| phase | JVM before | JVM after | Jolt before | Jolt after |
|---|---|---|---|---|
| search | 2 658 ms | 1 135 ms | 8 600 ms | 2 419 ms |
| apply | 4 278 ms | 3 169 ms | 11 861 ms | 8 300 ms |
| rebuild | 633 ms | 651 ms | 1 039 ms | 1 143 ms |
| total | 7 595 ms | 5 006 ms | 21 543 ms | 11 902 ms |

Search met the projection (3.6× on Jolt, 2.3× on the JVM). Apply did
not (1.4× on both), and its cost per match on the saturated AC-9
graph, where every right-hand side already exists, says why:

| per match, all hits | JVM | Jolt |
|---|---|---|
| search, compiled pattern | 296 ns | 709 ns |
| instantiate the right-hand side (two `add-node` hits) | 602 ns | 1 430 ns |
| one `add-node` hit: canonicalize, pack, map read, find | 225 ns | 427 ns |
| `find` on the match's class | 35 ns | 61 ns |
| the apply loop's destructuring and `try`, per match | 22 ns | 97 ns |
| one quiet apply through the runner | 754 ns | 1 760 ns |

Two map reads at 156 ns are a fifth of a Jolt match's apply; the rest
is spread over union-find reads, keyword reads of the e-graph's
fields (22 ns each on Jolt, the map being an array map still at
fourteen keys), `count` and `nth` on nodes, and the pair vectors
`instantiate` threads the graph through. No single row remains that
a change would pay against by more than a tenth; the candidate, if
apply is the next row, is threading the graph through a one-element box
instead of `[g id]` pairs and building an arity-two node in one
allocation, an estimated tenth of apply on Jolt. Beyond that the
constants are the runtime's ("The runtime itself", below).

Answered on the way, the open question of section 12: **the e-graph
stays a map.** On Jolt a keyword read of a fourteen-key map costs
22 ns and of a record 21.5, while `assoc` on the record costs 191
against 65 on the map and `update` 310 against 155; on the JVM the
record reads at 5 ns against 17 and writes a third faster. Jolt is
primary; maps.

### Rejected, each by a row above

- **An array open-addressing table for the memo**, inside a scope:
  212 ns per read on Jolt against 156 for the persistent map with the
  same key (an `aget` is 15 ns, a `==` 34, and the bucket arithmetic
  shifts), 37 against 39 on the JVM; and it would force a copy-in,
  copy-out scope around every phase. Not built.
- **`long-array`s for the union-find**, the earlier plan of this
  section: `aget` 15 ns against `nth` 20 at 152 003 entries on Jolt,
  and the array `find` prototype slower than the vector one. Arrays
  help writes on Jolt and not reads, so the scoped-array plan is
  withdrawn for reads and remains an option only for a write-heavy
  pass (the final pass of `rebuild`) if a row ever points there.
- **A sorted map** by fixnum key: 738 ns on Jolt.
- **A nested index**, operator to first child to a small map by
  second child: not measured as a whole; its innermost level is a
  fixnum-keyed map again (100 ns and up on Jolt at any size) and it
  touches every memo site. The candidate if the memo is the next row.
- **Packed fixnums as the e-node representation throughout**: saves a
  vector per node, but leaves and n-ary nodes stay vectors, a leaf
  number is indistinguishable from a packed node, and
  `compare-nodes`, printing and every analysis read nodes as vectors.
  Not now; the term seam keeps it possible.
- **Transients for the persistent writes**: 3% of samples; halving
  them buys one or two percent.

### The runtime itself

Four Jolt primitives are out of line with their neighbours and with
the JVM: hashing a fresh 3-vector (212 ns against 18), hashing a
fixnum (29 against 5), a shift (16, and 35 with the `bit-or`, against
0.1), and `==` (34 against `=` at 1.2 on the same fixnums). A
persistent map read with a fixnum key is 100 to 160 ns, and a
hash-array-mapped trie shifts and masks the hash at every level, so
the shift cost compounds. If Jolt is ours to change, these are the
highest-leverage fixes for every program on it, and the design above
stands after them: a packed key hashes one fixnum instead of three
values and allocates nothing. An open question.

### Measured: the apply phase, second pass (2026-09-25)

The row above left apply at 8.3 s of 11.9 on Jolt, with a candidate
(a box instead of `[g id]` pairs, a node in one allocation) estimated
at a tenth of it. Before building that, the phase was re-derived from
measurement. Three instruments: the AC-10 run with the runner's own
`:stats`; a copy of the runner's loop with a timer around every
`instantiate` and every `union`; and per-match rows on the saturated
AC-9 graph (18 669 nodes, 511 classes, 204 630 matches of the
associativity pattern), best of five. The scripts were scratch; the
numbers are the record.

**Where apply goes.** AC-10, ten iterations, 3 336 820 matches, of
which 136 376 merged two classes. A *hit* is an `instantiate` whose
right-hand side already exists; a *miss* adds at least one node.
Timer overhead (`System/nanoTime` is 117 ns on Jolt, 20 on the JVM)
is subtracted.

| | Jolt 0.8.12 | JVM (Clojure 1.12) |
|---|---|---|
| hits, 3 221 432 `instantiate` calls | about 4 750 ms | about 2 150 ms |
| misses, 115 388 | 1 470 ms | 520 ms |
| unions, 136 376 | 750 ms | 310 ms |
| the runner's loop around them | about 1 600 ms | about 300 ms |
| apply, uninstrumented | 8 555 ms | 3 279 ms |
| per hit at saturation (iterations 9 and 10) | about 1 700 ns | about 700 ns |

Iterations 8 to 10 hold 2.7 million of the matches and 5.3 s of
Jolt's apply; iteration 10 exists only to observe that nothing
changes. Unions move 1.07 nodes and 0.68 parents each on average
(145 473 nodes and 93 174 parents over the run), so a union's cost is
its constant, not its merging. There are twice as many misses as
final nodes because a match found in the snapshot and re-applied in
the working graph, after a union has moved one of its children, does
not find its right-hand side under the new canonical form (the memo
is re-keyed only at rebuild) and builds a duplicate, which rebuild
merges away: the node count peaks at 59 456 in iteration 7 and ends
at 57 012. egg's deferred rebuilding has the same property.

**The hit path, per match on AC-9** (ns; the small pieces are net of
the reduce and the three bindings reads they were measured with).

| | Jolt | JVM |
|---|---|---|
| search as written: `ematch`, match maps built | 634–649 | 282–285 |
| search, enumeration only: the callback counts | 316 | 142 |
| apply as written: the runner's loop, `try`, destructuring | 1 648 | 626 |
| `instantiate` (two `add-node` hits) | 1 420 | 571 |
| one `add-node` hit, node prebuilt | 417 | 199 |
| `canonicalize` of a prebuilt node | 123 | 63 |
| one memo read, real packed key | 120 | 47 |
| the same map, dense keys / random 60-bit keys | 115 / 128 | 47 / 44 |
| `hash` of a fixnum, in situ | 55–80 | 8–9 |
| three bindings reads, symbol keys | 60 | 49 |
| five `find-in` | 232 | 113 |
| five `[g id]` pairs | 115 | about 20 |
| two nodes by `conj`, `conj`, `term/make` / as literals | 200 / 36 | 80 / under 10 |
| `pat/compile` on a compiled pattern | 55 | 18 |
| the `try` around each match | 53 | 0 |

Three facts follow.

1. **The packed key is not the cost.** Dense and random keys read at
   the same speed. On Jolt the read is bounded by `hash` on a fixnum,
   55 to 80 ns in situ (29 in the isolated row above), because Jolt
   hashes fixnums with an exact port of Clojure's Murmur3 in Scheme
   (`host/chez/hasheq.ss`, "JVM-compatible hash engine"): the values
   must match the JVM's, so only its implementation could get
   faster, not its shape. A design on Jolt reads the memo as few
   times as a hit needs, twice for this right-hand side, and nothing
   keyed by a hashed value beats it (the nested index, below).
2. **Materializing matches is half of search** on both runtimes:
   `bindings-of`, the match map and the transient `conj!` cost 320 ns
   of 634 on Jolt and 140 of 285 on the JVM.
3. **The hit path as built is not decision 5.** Per match it builds
   two node vectors with `conj`, `conj` and `term/make` (100 ns each
   on Jolt against 18 for a literal), canonicalizes each inside
   `add-node` (a second `find` on ids the matcher just resolved),
   packs, reads the memo, calls `find`, allocates five `[g id]`
   pairs, re-checks that the pattern is compiled, reads four keyword
   fields of the e-graph map per node, and destructures inside a
   `try`. Decision 5 said the compiled `instantiate` would compute
   keys from the registers and build no node unless new; what shipped
   reads a bindings map, builds nodes and calls `add-node`. That is
   why apply missed its projection and search met it.

**Floors, measured as prototypes on AC-9**, per match, both phases:

| | Jolt | JVM |
|---|---|---|
| as written: `ematch` then apply | 2 237–2 282 | 918–945 |
| A: apply from the bindings map straight to packed keys, no node built; search unchanged | 634 + 638 = 1 272 | 282 + 309 = 591 |
| A′: search writes the registers into a flat `long-array` (class root and one slot per variable per match); apply reads it and instantiates by packed lookups | 361 + 489 = 850 | 148 + 226 = 372 |
| B: search and apply fused in the matcher's callback, no match representation at all | 779 | 295 |

A′ is within a tenth of B on Jolt and keeps the two phases: the
scheduler sees the count before anything is applied, guards and
computed right-hand sides see the snapshot, `:stats` keep their
meaning. B would run the enumeration twice under backoff. A′ is the
decision.

**The applied path**, per operation, the realistic case: a fresh
node, then the union of its singleton class into the matched class.

| | Jolt | JVM |
|---|---|---|
| `add-node` miss | 3 330 | 984 |
| the union after it | 1 960 | 690 |
| of the miss: `conj` on `:uf` / on `:size` | 265 / 266 | 100 / 82 |
| `conj` of the class map on `:classes` | 391 | 166 |
| memo `assoc`, packed key | 699 | 238 |
| a parent `assoc` through `update-in [:classes c :parents]`, per child | 900 | 278 |
| `:by-op` `conj` | 600–730 | 180–200 |
| of the union: `assoc-in` on `:uf`, on `:classes` twice | 443, 483, 507 | 146, 122, 140 |
| `:by-op` `disj` then `conj` | 1 114 | 194 |
| `:pending` `conj`; one node merged into a 500-node set | 283; 288 | 59; 140 |

Seven persistent writes per fresh node and five per union, 265 to
1 100 ns each on Jolt: 2.2 s of the 12.2. The `conj!` row (55.6 ns)
puts a transient scope over apply and rebuild at about half of that.
Deferred, below.

**Stale matches.** A match every node of which existed in the
previous iteration's rebuilt graph, with the same canonical children
and in the same class, was found and applied then; applying it again
can only build a duplicate that rebuild merges (the trace above).
Counted with lookups in the previous graph, which the runner has for
free because the e-graph is a value:

| iteration | matches | fresh |
|---|---|---|
| 7 | 450 435 | 398 129 |
| 8 | 868 714 | 560 158 |
| 9 | 931 610 | 166 412 |
| 10 | 931 502 | 148 |
| all ten | 3 336 820 | 1 272 302 |

Saturating AC-6 to AC-9 with and without the filter gives identical
node and class counts after every iteration and the same number of
iterations, applying 46% of the matches. (A class-level test, any
class whose node set changed, is also sound but keeps 78%: a few
re-keyed parents mark a hub class as changed.) The argument: unions
only grow classes, so what the earlier application put into the
matched class is still there. Two conditions: the filter compares
against the last iteration in which the rule was actually applied,
since backoff drops matches; and it covers only pattern rules without
a guard or a computed right-hand side, since analysis data can change
under a stale match. In the cheap form, two lookups in the previous
graph per match, it costs about what A′'s apply hit costs and buys
nothing. The form that pays keeps an iteration stamp per node in the
class's node map (`:nodes` as node → stamp, refreshed when a node is
moved or re-keyed) and reads it in the matcher as it visits, skipping
the callback. After A′ the hit path is about 1.6 s of 6 on Jolt and
the filter removes 60% of it; seeding the search from fresh nodes
through `:parents` (semi-naive; the relational matcher of section 6)
removes the same fraction of search. Both second-order, both after A′.

**Decisions (2026-09-25, second pass; built the same day).**

1. **Flat match buffers in the runner (A′).** A compiled pattern rule
   carries its plans and a stride, one plus its variable count. Its
   search fills a `long-array` (grown by doubling, kept per rule
   across iterations) with the class root and the registers of each
   match; the count is the length over the stride and is what the
   scheduler and `:stats` see. `ematch` keeps its public shape; the
   runner does not call it for pattern rules. A guard or a computed
   right-hand side receives a bindings map built from the buffer for
   that match, so only rules that have one pay. Searcher rules are
   unchanged.
2. **Register-based `instantiate`.** The right-hand plan is walked
   with the registers on the working graph: a variable is `find-in`
   of its register; a compound node of arity two or less whose
   operator is interned computes the packed key and reads `:memo`; a
   hit yields `find-in` of the stored id; a miss, an unknown operator,
   a leaf or a wider node builds the node and calls `add-node` as
   today. `:uf` and `:memo` are read once per match (a union or a
   miss changes them). No node vector, no `[g id]` pair, no
   `canonicalize` and no `compile` check on the hit path; the working
   graph is a loop variable. The public `instantiate` loads the
   registers from its bindings map and runs the same walk: one
   implementation.
3. **Rules for hot code, added.** On the JVM an `aset` into a
   `long-array` whose value the compiler cannot see as `long` is
   reflective and costs about 3 µs (the flat search measured 2 989 ns
   per match before a `long` cast, 148 after); cast first. Per-match
   timing belongs in an instrumented copy of the runner, never in it.

Projection from the AC-9 rows: Jolt search 2.5 → 1.2 s and hits
4.75 → 1.6 s, misses, unions and rebuild unchanged, about 6.2 s from
12.2; JVM about 2.7 s from 5.1. The search projection held last
time; the apply one did not because decision 5 was not built as
written. The prototype rows above are the code paths as they would
ship, less the miss fallback and the scheduler plumbing.

**Measured when built** (2026-09-25, the same day), AC-10, the
runner's `:stats`:

| phase | JVM before | JVM after | Jolt before | Jolt after |
|---|---|---|---|---|
| search | 1 134 ms | 551 ms | 2 516 ms | 1 361 ms |
| apply | 3 279 ms | 2 337 ms | 8 555 ms | 4 498 ms |
| rebuild | 684 ms | 711 ms | 1 152 ms | 1 152 ms |
| total | 5 124 ms | 3 632 ms | 12 263 ms | 7 050 ms |

Search met its projection on both runtimes. Apply did not quite: a
hit at saturation (iteration 10) costs 720 ns on Jolt and 430 on the
JVM against the prototypes' 489 and 226. The built functions on AC-9
say where: `ematch-flat` 361 and 136 ns per match (the prototype 361
and 148); `apply-flat` 707 and 385 (489 and 226). The difference is
the plumbing the prototypes lacked: the instruction loop's `nth` and
`case`, the `packed-key` call in place of inline arithmetic, a third
keyword read (`:ops`) per match, and the register loads from the
buffer with the cell that names a failing match (91 ns together on
Jolt). About 200 ns per hit on both runtimes, 0.65 s of Jolt's 7.05;
a closure-compiled program would recover part of it. The bench's
ac-sum 10 row reads 7 060 ms on Jolt and 3 287 on the JVM, the JVM
warm from the earlier fixtures. Suites unchanged and green on both
runtimes, cromulent 49 tests and 172 assertions, bendix 70 and 366.
Apply is still the largest phase on Jolt, about 2.25 s of hits,
1.5 s of misses and 0.75 s of unions, so the applied path and then
the stale filter stand as the next rows, in that order.

**Rejected or deferred, each by a row above.**

- **The box and the one-allocation node**, the earlier candidate:
  115 ns of pairs and 164 ns of node building out of 1 648, 17% of
  the hit path, measured. A′ removes both and the rest. Superseded.
- **A nested memo index**, operator → first child → second child: the
  innermost level hashes the second child, and the hash is the read's
  cost (120 ns against 115 with dense keys); a scan or binary search
  over up to 511 second children costs more than the hash. Rejected
  by the `hash`, `nth` and `=` rows.
- **The stale filter by previous-graph lookups**: the cost of the
  thing it skips. **Per-node stamps and semi-naive search**: deferred,
  second-order after A′, numbers above.
- **A transient scope over apply and rebuild**: ceiling about 1 s of
  12.2 on Jolt. Deferred until the applied path is the largest row.
- **`union` updating `:by-op` per node of the smaller class** rather
  than per operator: 1.07 nodes per union here; nothing to gain until
  the AC experiments merge large classes.

### Measured: Jolt 0.8.13 (2026-09-27)

The same AC-10 run, over the same hot path as the run measured
above. Each figure is the median of three runs of the runner's
`:stats` after a warm-up (ac-sum 8), on the same machine as before:

| phase | JVM 09-25 | JVM now | Jolt 0.8.12 (09-25) | Jolt 0.8.13 | lambda-microegg |
|---|---|---|---|---|---|
| search | 551 ms | 556 ms | 1 361 ms | 1 369 ms | 350 ms |
| apply | 2 337 ms | 2 245 ms | 4 498 ms | 3 913 ms | 1 000 ms |
| rebuild | 711 ms | 641 ms | 1 152 ms | 986 ms | 152 ms |
| total | 3 632 ms | 3 481 ms | 7 050 ms | 6 262 ms | about 1 500 ms |

Jolt is 11% faster in total. Apply is 13% faster and rebuild 14%;
search did not move, so the gain is in the applied path and the
unions. The code did not change, so the upgrade is the likely
cause, but 0.8.12 was not rerun beside it. The JVM is within noise of
its earlier run. Against lambda-microegg, the JVM is 2.3 times slower
and Jolt 4.2 times, where the first measurement of this section read
5.1 and 14.4. Rebuild is now the furthest phase on both runtimes,
4.2 and 6.5 times. The lambda-microegg figures come from its
author's machine, so only the ratios between this project's own
columns compare like with like.

### What persistence still buys, unchanged

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

`cromulent.pattern`. The public API: `(ematch g p)` returns a vector
of `{:class root :bindings {?a root ...}}`; `(match-class g p id)` the
bindings for one class; `(instantiate g p bindings)` goes the other
way, returning `[g' id]`, and calls `add-node` as it walks rather
than building a term, because a term with ids at its leaves would
read as integer constants. Each accepts a pattern or its compiled
form. Behind that API (decided and built 2026-09-25, section 5) a
pattern is **compiled once** into a plan and matched by index loops:

- `(compile p)`: variables become register numbers in order of first
  occurrence (registers as in egg's e-matching machine; the word slot
  is kept for slotted e-graphs, which this is not); a compound sub-pattern becomes its operator, arity and
  child plans; a leaf becomes itself and is matched by membership in
  a class's node set, as before. The plan is nested vectors,
  `[:var register symbol]`, `[:node op arity plans]`, `[:leaf value]`,
  read with `nth`. (The design had a ground sub-pattern resolved to a
  class id by one lookup per search; on a graph with unions pending
  that lookup can miss a node the structural walk finds, so ground
  parts are matched structurally like everything else. They are rare
  in rules and the saving was not measurable.)
- Candidate classes come from `:by-op` for the pattern's operator; a
  bare variable matches every root; a ground pattern is its lookup.
  Within a class the matcher reduces over `:nodes`, tests operator
  and arity with `nth` and `count`, and matches children pairwise by
  index. The registers live in one `long-array` per search, −1 for
  unbound, written on bind and restored on backtrack; a repeated
  variable compares ids with `=`. Child ids are taken as they are
  when the graph is clean and passed through `find` otherwise
  (section 5, decision 3). Each match is delivered to a callback with
  the registers; `ematch` copies them into a bindings map per match,
  and `ematch-flat` writes the class root and the registers into one
  flat `long-array`, stride one plus the variable count, grown by
  doubling and reused across a run, which is what the runner reads
  for pattern rules (section 5, second pass).
- The compiled form also holds a program for instantiation: a
  post-order list of `[:leaf value dest]` and
  `[:node op operand-registers dest]` over one register file,
  variables first and temporaries after (`:program`, `:result`,
  `:nregs`). `instantiate-registers` runs it: a node of arity two or
  less is looked up by its packed key (`core/packed-key`), with
  `:uf`, `:memo` and `:ops` read once per call and again after a
  miss; a hit is `find-in` of the stored id; only a miss, a leaf, a
  wider node or an unknown operator builds a node and calls
  `add-node`. `instantiate` loads the registers from a bindings map
  (the rule constructor already checks that every right-hand
  variable is bound on the left) and runs the same program; the
  runner loads them from the buffer. A right-hand side is compiled
  with its left-hand side's `:vars` fixed, so both read the same
  registers.
- The runner compiles each rule's pattern sides once per `embiggen`
  call, a right-hand pattern against its left-hand side's registers,
  in its own copies of the rule maps; the caller's rules stay plain
  data.

Later, by benchmark: the relational e-matcher (Zhang et al. 2022).
It would not change the API.

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
are measured against. A pattern rule's matches travel between the
phases as a flat buffer, `{:buf long-array :n count}`, never as maps;
a searcher's are a vector of maps; `match-count` counts either, and
`[]` from a scheduler means none. A guard or a computed right-hand
side is handed a bindings map built from the buffer for its match,
so only rules that have one pay for maps.

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

`cost-fn` is `(fn [e-node child-costs] cost)`; the default is AST
size. A cost is any value `compare` orders: a number, or a vector for
a lexicographic cost such as bendix's `no-D` (../bendix/IDEA.md
section 6), and the extractor compares costs with `compare`. Bottom-up fixpoint over all classes, egg's Extractor, costs in a
vector indexed by class id: iterate until no class's best cost
changes; a node whose child has no cost yet is skipped, which is why
cycles (`x = x + 0`) are harmless. Then rebuild the term top-down from each class's best node.
`extractor` returns a function of a class id that shares one cost
table across many extractions; `yoink` is `extract`'s alias. Ties
between equal-cost nodes go to the smaller node under
`cromulent.term/compare-nodes`, a total order that is the same on
every runtime, so extraction is a function of the e-graph value. It
is not, however, the same across runtimes when costs tie: the order
compares child *ids*, and which id survives a union depends on the
order matches are applied, which follows hash iteration order
(reductions over `:by-op` sets and `:parents` maps) and differs per
runtime. Costs, counts and per-rule totals agree everywhere; a
term is runtime-stable when its minimum is unique. An id-free
tie-break (comparing the built terms) is a later, benchmarked change. The cost
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
- **The third runtime**: `cromulent.smoke` (`src/`, `.cljc`) is a
  vector of runtime-stable facts about fixed runs, plain data;
  `cromulent.smoke-test` asserts it on the JVM and Jolt, and orrery's
  node build (`npm run smoke` in ../orrery) prints the same rows on
  ClojureScript. Never ids, never a tied term.

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
- Records vs maps on Jolt: measured 2026-09-25, maps (section 5,
  "Answered on the way").
- One key layout or two, for ClojureScript: measured 2026-09-25, one
  (section 5, decision 2).
- **Retiring the packed key** (asked 2026-09-25):
  keying the memo by the canonical node itself would remove `:ops`,
  `:op-names`, `:memo-other` and the two limits. The second pass
  found "the packed key is not the cost" about its shape; what it
  buys is the fresh-vector hash on every right-hand-side lookup: a
  memo read with a vector key built fresh is 423 ns on Jolt and 108
  on the JVM against 199 and 74 packed on the spot (section 5, the
  first table), and `instantiate-registers` reads the memo from the
  registers without building a node at all. Over the roughly six
  million lookups of AC-10 that is on the order of a second on Jolt
  and a few hundred milliseconds on the JVM. A bench row's decision,
  when simplicity is wanted more than that.

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
  `ast-size`, deterministic ties (section 8); costs ordered with
  `compare`, so a vector is a lexicographic cost (2026-09-13, for
  bendix's `no-D`).
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

  | fixture | n | JVM | Jolt 0.8.13 |
  |---|---|---|---|
  | add-terms (random terms, depth ≤ 4; 35 967 distinct nodes) | 20 000 | 210 ms | 287 ms |
  | ematch `[:+ ?a [:* ?b ?c]]` on the above (4 557 matches) | | 24 ms | 20 ms |
  | ematch `[:+ ?x ?x]` on the above (32 matches) | | 12 ms | 13 ms |
  | union + rebuild (random unions on the above) | 2 000 | 111 ms | 104 ms |
  | extract, cost table for every class of the above | 35 967 | 50 ms | 70 ms |
  | embiggen, egg README rules on the above, 2 iterations (→ 45 282 nodes, 22 871 classes) | 2 | 822 ms | 1 105 ms |
  | chain-collapse (2 000-atom sum, all atoms unioned) | 2 000 | 8 ms | 17 ms |
  | ac-sum, saturate a 7-atom sum under comm + assoc (127 classes, 1 939 nodes, 8 iterations) | 7 | 49 ms | 85 ms |
  | ac-sum, the same with 8 atoms (255 classes, 6 058 nodes, 9 iterations) | 8 | 175 ms | 360 ms |
  | ac-sum, 10 atoms (1 023 classes, 57 012 nodes, 10 iterations): the yardstick of section 5 | 10 | 3 414 ms | 6 379 ms |

  Measured 2026-09-27 on Jolt 0.8.13 (section 5 compares it with
  0.8.12). On 2026-09-25, after the second pass (flat match buffers
  and the register program, section 5) landed, on Jolt 0.8.12: egg
  rules 802 and 1 315 ms, ac-sum 7 52 and 100, ac-sum 8 175 and 418,
  ac-sum 10 3 287 and 7 060. After the first pass
  alone, compiled patterns and packed keys: egg rules 747 and
  1 380 ms, ac-sum 7 64 and 137, ac-sum 8 246 and 623, ac-sum 10
  5 047 and 11 745; before both, on the same machine: ematch 57 and
  68 ms, ac-sum 8 361 and 1 717 ms, ac-sum 10 7 511 and 21 090 ms. The
  ac-sum rows are experiment 1 of ../design/ac-problem.md, the
  baseline. The embiggen row is where the class-level worklist was
  caught (section 4); the ac-sum 10 row is where the fresh-key
  hashcons lookup and the interpreted matcher were caught (section
  5).

Compiled patterns and packed hashcons keys (2026-09-25, sections 5
and 6, green on both runtimes, the suite unchanged at 49 tests and
172 assertions and bendix's at 70 and 366): `cromulent.pattern`
compiles a pattern to a plan and matches with a register array and index
loops, `ematch`, `match-class` and `instantiate` taking a pattern or
its compiled form; `cromulent.core` keys the hashcons by a packed
fixnum for nodes of arity two or less (`:memo`, with `:ops` and
`:op-names` interning operators) and by the node for leaves and
wider nodes (`:memo-other`), exposes `find-in` over the union-find
vector and `memo-entries` for the checker, and `canonicalize` is an
index loop; `cromulent.rewrite` compiles each rule's pattern sides
once per run; `cromulent.term/make` builds small nodes without
`into`; the checker verifies the operator table and reads the
hashcons through `memo-entries`. The bench gained the ac-sum 10 row.
bendix's bench rows are unchanged or faster on both runtimes.

Flat match buffers and the register program (2026-09-25, section 5
second pass and section 6, green on both runtimes, the suites
unchanged at 49/172 and 70/366): `cromulent.pattern/compile` takes
fixed variables and emits an instantiation program; `ematch-flat`
writes matches as class root and registers into a reusable
`long-array`; `instantiate-registers` runs the program with
packed-key lookups and `add-node` only on a miss, and `instantiate`
is a wrapper over it; `cromulent.core/packed-key`;
`cromulent.rewrite` compiles a right-hand pattern against its
left-hand side's registers, keeps one buffer per pattern rule per
run, applies flat matches without allocating on a hit, and counts
matches with `match-count`. AC-10: Jolt 12.3 → 7.1 s, JVM 5.1 →
3.6 s.

Portable to ClojureScript (2026-09-25, for ../orrery; sections 1, 5
decision 2, 8, 10; green on both primary runtimes, 51 tests and 204
assertions, bendix unchanged at 70/366): the six source namespaces
renamed `.clj` → `.cljc` with no change but the port's four edits;
the packed key narrowed to `op·2^42 + a·2^21 + b` with the bench
medians unchanged; `cromulent.platform` (the clock) as the one
conditional file; backoff doubling by `times-pow2`; the two `catch`
clauses conditional; `cromulent.smoke`, 28 runtime-stable facts,
asserted by the suite here and by orrery's node build (all 28 pass,
54 ms, zero compiler warnings on the engine). The tests and the bench
stay `.clj`.

The runner as start/step/finish (2026-09-25, section 7, for orrery's
lesson 5; 52 tests, 210 assertions on both runtimes):
`cromulent.rewrite/start` compiles the rules, initializes the
scheduler and rebuilds the input; `step` runs one iteration with the
limit checks in `embiggen`'s order; `finish` returns the result map;
`embiggen` is the loop over the three, so a caller that steps a run
from a timer gets exactly the run one call would make, bans and all.

The exporter (2026-09-26, for ../orrery; 57 tests, 250 assertions on
both runtimes): `cromulent.export`, the e-graph in the egraph-serialize
JSON format that egg, egglog and the egraphs-good tools share.
`serialize` gives the data with string keys, `json` the text, and
`->json` is a printer of its own, so the same text comes out on the
JVM, on Jolt and in ClojureScript and no runtime prints a ratio; a
node is named `class.i` in `compare-nodes` order and a child is the
first node of its class, as egg names them; options give the cost
function (each node the cost of the cheapest term it heads, when a
number), the roots, the class data (a bendix graph's polynomials)
and how operators and leaves print. One smoke fact pins the text of
`2·x + y` across the three runtimes.

Not yet: explanations, relational e-matching; the AC experiments
beyond 1–3 live in bendix. CI workflow is written but the repository
has no remote.
