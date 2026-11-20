# Snapshots: an e-graph as data on disk

A proposal, written 2026-11-19. It adds "Snapshots" to IDEA.md
section 11.

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
