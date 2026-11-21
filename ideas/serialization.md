# Snapshots: an e-graph as data on disk

A proposal, written 2026-11-19. Built 2026-11-20 as
`cromulent.snapshot`: sections 3 and 5 as written, apart from what
section 6 records the building decided; section 6 also lists what
is still open. It fills in "Snapshots" in IDEA.md section 11.

## The short of it

- An e-graph is already a value; a snapshot makes it a value that
  outlives the process. Long saturations survive time limits, memory
  limits and restarts; e-graphs move between machines; tests and
  explorers load fixtures instead of rebuilding them.
- The core needs almost nothing. Everything in the e-graph map is plain
  data except `:analyses`, whose maps hold functions. A snapshot is the
  map without them, plus their names; restoring takes the analyses
  from the caller, as `egraph` does.
- Encoding stays outside the core: the core returns data, the caller
  picks EDN, Transit, Nippy or Fressian. cromulent keeps no
  dependencies.

## 1. Why it is worth having regardless

- **Resuming.** ribbon's n = 9 saturation ran out of a 10 GB heap after
  65 minutes and kept nothing (../ribbon/COMPLEXITY.md, 2026-11-19). A
  snapshot every k iterations bounds what a crash or a time limit
  costs. Keeping the e-graph in a REPL does the same until the process
  dies; a snapshot survives that too.
- **Moving.** Work happens on more than one machine. A saturated
  e-graph is the expensive artefact; a snapshot ships it.
- **Fixtures.** Tests and benches that saturate the same input every
  run can load it. orrery and snail-crawl saturate in the browser
  (snail-crawl's lesson 4 stops at n = 7 because n = 7 takes 2 s); a
  snapshot computed once on the JVM loads instead.
- **Inspection and diff.** A snapshot is a file to compare, grep and
  keep with a result, so a bench row can carry the e-graph it measured.

## 2. What is there already (measured 2026-11-19)

On a saturated ribbon e-graph at n = 5 (85 nodes, two analyses,
bendix's `:ratfun` and ribbon's `:fingerprint`):

- No atoms, records or other non-data values anywhere in the map.
- `:analyses` holds six functions (bendix's `ratfun-analysis`
  closures). Nothing else does.
- `(dissoc eg :analyses)` printed as EDN and read back is `=` to the
  original, on the JVM. Numbers are Longs, Ratios and a few Integers,
  which read back as Longs and still compare equal.
- About 240 bytes of EDN per node (20 KB for 85 nodes), so millions of
  nodes are gigabytes of text: EDN is for small e-graphs and fixtures,
  a binary encoding for large ones.

## 3. Design

```clojure
(snapshot eg)                 ;; => {:cromulent/snapshot 1
                              ;;     :analyses [:ratfun :fingerprint]   ; names, in order
                              ;;     :egraph {...}}                     ; the map, :analyses removed
(restore snap {:analyses [a b]})  ;; => eg; throws unless the names match, in order
```

Names are placeholders, to be settled when built.

- **The contract grows one clause.** Analysis data and
  `:analysis-state` must be data: no functions, atoms or host objects.
  bendix's analysis meets it already. An analysis that cannot is
  refused by `snapshot`, naming the analysis, rather than written and
  failing on restore.
- **Any state, not only rebuilt.** A snapshot of an e-graph with
  pending work restores with the same pending work; `rebuild` after
  `restore` gives what `rebuild` before `snapshot` would have. Tests
  check `check/violations` on every restored e-graph.
- **Packed keys travel as they are.** `:memo` is keyed by
  op-index·2^42 + a·2^21 + b, and `:ops` and `:op-names` are in the
  snapshot, so the keys stay valid. They fit in 2^53, so a snapshot
  made on the JVM restores in ClojureScript.
- **The runner's state is separate.** `embiggen` keeps an iteration
  count, stats and, under the backoff scheduler, its bans; none of it
  is in the e-graph. Resuming a run exactly needs it too: a
  `(snapshot-run run)` with the same shape, or `embiggen` accepting a
  run to continue from. Rules that keep their own state (ribbon's
  remember which sums they have handled) are the caller's to save;
  resuming without it is correct, only slower.
- **Timelines lose sharing.** Retained iterations share structure in
  memory; written out, each is whole. Incremental snapshots, a base
  plus diffs (`diff` is a set difference on `:memo` already), are a
  later step if timelines on disk are wanted.

## 4. Portability

- Ratios: ClojureScript has none. A snapshot holding them restores on
  the JVM and Jolt; for the browser, analyses that keep exact
  rationals already use their own representation (bendix.num), which
  is data and travels.
- Jolt: EDN reading and writing exist; a binary encoding there is
  open.

## 5. Tests

- Round trip: `(= eg (restore (snapshot eg) opts))` on random e-graphs
  (section 10's generators), through EDN.
- Resume: saturating k iterations, snapshotting, restoring and
  saturating the rest gives the same e-graph as saturating straight
  through, under the simple scheduler.
- A refused snapshot: an analysis keeping a function in its data.
- The smoke facts: one restored fixture on all three runtimes.

## 6. What the building decided (2026-11-20)

- **Names.** `snapshot` and `restore` for e-graphs, `snapshot-run`
  and `restore-run` for runs, in `cromulent.snapshot`, which sits
  above `cromulent.rewrite` as `cromulent.explain` does. The core
  gained only the contract clause, in `egraph`'s docstring. The
  envelopes are `{:cromulent/snapshot 1 ...}` and
  `{:cromulent/run-snapshot 1 ...}`; `restore` refuses any other
  version, and a malli schema (`snapshot-schema`) checks the
  envelope's shape.
- **The whole map is checked, not only the analyses.** Leaves,
  operators and journal reasons are the caller's values too, so
  `snapshot` walks everything and refuses with the path and the
  value, naming the analysis when the path is under a class's
  `:data` or `:analysis-state`. On a saturated sum of eight atoms
  (6 058 nodes, no analyses) the walk takes 2.1 ms and `pr-str`
  22 ms, which is 75 bytes a node, so the check costs about a tenth
  of the cheapest encoding. A first version tested `inst?` before
  the collections and took 80 ms: `inst?` is a protocol check, slow
  when it fails.
- **Runs resume exactly.** `restore-run` takes the rules (the same
  names, in order) and the options again, calls `start`, and puts
  back the scheduler's state, `:seen` (the epoch each rule last
  applied at), the stats and the elapsed time. The timeline comes
  along, each e-graph whole. A run snapshotted after any number of
  iterations, sent through EDN and restored finishes as the run
  straight through did, under both schedulers: the same e-graph,
  stop reason, iterations and stats, timings aside (a property over
  random rules, and the sum of five after every iteration). Dropping
  the scheduler's state or `:seen` on restore fails that property.
- **The limits count the whole run.** `:iter-limit` counts its
  iterations and `:time-limit-ms` its time, the time between snapshot
  and restore excepted, so going on past a limit means restoring
  under a higher one. A stop reason that still holds is kept:
  `:saturated`, and `:node-limit` while the e-graph has more nodes
  than the limit given. Clearing every stop reason, the first idea,
  would have made a run capped by nodes take one more iteration on
  restore under the same options.
- **The smoke facts.** `cromulent.smoke` carries a snapshot written
  on the JVM as EDN text (egg's README rules on 0 + 1·a, packed keys
  past 2^32) and reads it at run time, so the fact checks the
  reader on each runtime, and a run of the sum of five saved after
  three iterations under backoff and finished. Both hold on the JVM,
  Jolt and ClojureScript (orrery's node build). Reading EDN is the
  smoke namespace's one reader conditional: `clojure.edn` or
  `cljs.reader`.

Still open:

- Incremental snapshots (a base and diffs) for timelines on disk.
- A binary encoding on Jolt, and a measured one on the JVM for large
  e-graphs: EDN at 75 to 240 bytes a node is still gigabytes at
  millions of nodes.
- ribbon's resume: saving every k iterations of the n = 9 run, with
  its rules' own state, is the first real use and the test of
  section 1's claim.
