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
both runtimes, and Jolt is the primary target (the Captain's own
usage, 2026-09-25): a change must pay on Jolt. Nothing earlier in
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

Two facts locate the cost. Search is read-only and is the worst phase
by ratio; rebuild, where every persistent write happens, is the best.
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
transducer, per element; multiply and never shift, to pack; `=` and
never `==` on ids; never build and hash a fresh vector in a hot path;
resolve a pattern's symbols once and never per visit.

### Decisions (2026-09-25; built the same day)

1. **Compiled patterns** (section 6). A scratch prototype, index loops
   over node children, variables as registers in a `long-array` restored
   on backtrack, no `find` on the children of a rebuilt graph, a
   callback per match, found the same 204 630 matches of the
   associativity pattern on the saturated AC-9 graph in 35.9 ms
   against 148.9 as written on the JVM, and in 121.6 against 508.7 on
   Jolt: 4.1× and 4.2×.
2. **Packed hashcons keys.** The memo is keyed by a fixnum for a
   compound node of arity two or less: `op·2^48 + a·2^24 + b`, by
   multiplication and addition, since shifts cost 16 to 35 ns on
   Jolt; an absent child is written as 2^24 − 1; the sum stays under
   2^60 and so is a fixnum on Chez. Operators are interned per e-graph
   in `:ops` (operator to index) and `:op-names` (index to operator),
   assigned on first `add-node`; ids are bounded at 2^24 − 2 and
   operators at 2^12, far past any limit in use, and either overflow
   throws. Leaves and nodes of arity three or more keep the node
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
values and allocates nothing. Open question for the Captain.

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
  the registers; `ematch` copies them into the bindings map, and the
  runner's pattern-to-pattern path hands them straight to the
  compiled right-hand side.
- `instantiate` walks the right-hand side's plan (the rule
  constructor already checks that every right-hand variable is bound
  on the left), reads each variable from the bindings map, builds
  each compound node from its children's ids and hands it to
  `add-node`, whose hit path packs the key and reads the map once.
- The runner compiles each rule's pattern sides once per `embiggen`
  call, in its own copies of the rule maps; the caller's rules stay
  plain data.

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
- Records vs maps on Jolt: measured 2026-09-25, maps (section 5,
  "Answered on the way").

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

  | fixture | n | JVM | Jolt 0.8.12 |
  |---|---|---|---|
  | add-terms (random terms, depth ≤ 4; 35 967 distinct nodes) | 20 000 | 211 ms | 336 ms |
  | ematch `[:+ ?a [:* ?b ?c]]` on the above (4 557 matches) | | 25 ms | 20 ms |
  | ematch `[:+ ?x ?x]` on the above (32 matches) | | 14 ms | 14 ms |
  | union + rebuild (random unions on the above) | 2 000 | 112 ms | 138 ms |
  | extract, cost table for every class of the above | 35 967 | 50 ms | 84 ms |
  | embiggen, egg README rules on the above, 2 iterations (→ 45 282 nodes, 22 871 classes) | 2 | 747 ms | 1 380 ms |
  | chain-collapse (2 000-atom sum, all atoms unioned) | 2 000 | 9 ms | 20 ms |
  | ac-sum, saturate a 7-atom sum under comm + assoc (127 classes, 1 939 nodes, 8 iterations) | 7 | 64 ms | 137 ms |
  | ac-sum, the same with 8 atoms (255 classes, 6 058 nodes, 9 iterations) | 8 | 246 ms | 623 ms |
  | ac-sum, 10 atoms (1 023 classes, 57 012 nodes, 10 iterations): the yardstick of section 5 | 10 | 5 047 ms | 11 745 ms |

  Measured 2026-09-25 after compiled patterns and packed hashcons
  keys landed (before them, on the same machine: ematch 57 and 68 ms,
  ac-sum 8 361 and 1 717 ms, ac-sum 10 7 511 and 21 090 ms). The
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

Not yet: explanations, relational e-matching; the AC experiments
beyond 1–3 live in bendix. CI workflow is written but the repository has no
remote.
