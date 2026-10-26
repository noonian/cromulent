# Explanations and a proof checker

A proposal, written 2026-10-05. Sections 1 and 2 are built
(2026-10-25): the journal in `cromulent.core`, explanations in
`cromulent.explain`, the checker in `cromulent.derivation`; section
5 records what the building decided, the name among it. Sections 3 and 4 are as written.
It fills in "Explanations" in IDEA.md section 11, which
../bendix/IDEA.md calls "cromulent's explanations milestone".

## The short of it

- **Explanations** need the core to record what it now throws away:
  an opt-in journal of node births and unions. Everything else is a
  namespace above the core. Worth building.
- **A proof checker** is about a hundred lines and must not depend on
  `cromulent.core`. Worth building with explanations, as their test
  oracle.
- **Theory solvers** need nothing from the core: the e-class analysis
  contract is that seam, and bendix's polynomial analysis already is
  one.
- **A prover** is not worth building alone: its worth is a kernel and
  a library of proved lemmas, not its e-graph. As an adapter for
  [ansatz](https://github.com/replikativ/ansatz), which has both, it
  is a later experiment, gated on explanations.

## 1. Explanations

An explanation of `s = t` is a derivation: a chain of steps, each a
rule applied under some bindings, an asserted equation, a merge an
analysis made, or congruence over the steps for the children.

### What the core discards today

- `union` resolves both ids to roots at once and keeps neither the
  ids it was given nor a reason.
- `retire` makes the congruence unions inside `rebuild`; nothing
  outside the core sees which two nodes met.
- `process-pending` rewrites a stored node to its canonical form, so
  the term the id was born as is gone.
- The matcher and `instantiate` each know the id of the node they
  found and report its class root, so the runner unions two roots. A
  step needs the two nodes, the rule's name and the bindings.

Already in place: a node is named for good by the id it was born
with, and every id is some node's birth id.

### The seam: a journal

With an option at construction, the core records two things:

- **Births.** Node id → the node as `add-node` stored it. Its
  children are birth ids too, so the id denotes one term for good.
- **Unions.** `[a b reason]` for every union that merges two classes,
  `a` and `b` the nodes the reason is about. The writers are the
  callers of `union` (the runner, analyses, the user), each with its
  own reason, and `retire`, with `:congruence`.

Because only merging unions are recorded, the journal is the edge
list of a forest: the proof forest of Nieuwenhuis and Oliveras and of
egg's `explain`, with no extra structure and no re-rooting, since the
tree can be built from the vector when someone asks. A congruence
edge held because its nodes' children were equal when it was
recorded, so its sub-proofs use only earlier edges and the expansion
terminates.

Assert `a = b` with `f(a)` and `f(b)` present, then rebuild:

```clojure
;; journal                           ;; (explain g f-a f-b), as data
[[a   b   {:asserted "a = b"}]       [:cong :f [[:asserted "a = b" a b]]]
 [f-a f-b :congruence]]
```

### Above the seam

A namespace that reads the journal and

- builds the forest and finds the path between two ids, expanding
  each congruence edge into the proofs for its children;
- treats a rule edge as the rule's instance up to congruence at both
  ends: the matched node was born with the children its classes had
  then, not with the terms the bindings name now;
- answers for terms and not only ids: `[:f a]` and `[:f b]` are one
  id once `a = b`, so a question about two terms begins and ends
  with a congruence step;
- returns the proof as data, to check, print, or draw in orrery.

### What it costs

- One `conj` per new node and per merging union when recording is
  on, nothing when it is off. Both are bench rows to measure, on both
  runtimes, before the option is kept.
- `union` gains an optional reason; a caller that omits it yields a
  step that says only "asserted".
- The flat match buffer carries the matched node's id, and the apply
  path that allocates nothing on a hit allocates a reason per merging
  match.
- Every layer above must give reasons. bendix unions from
  `index-form`, `solve` and `materialize`; "by ring normalization" is
  the part ../bendix/IDEA.md already calls open.
- Proofs are as long as the union order made them (Flatt et al. 2022,
  arxiv.org/abs/2209.03398).

## 2. A checker

Five rules: reflexivity, symmetry, transitivity, congruence, and
"rule R under these bindings". Given a proof, the rule set and two
terms, it says whether the proof derives one from the other. It needs
`cromulent.term` and substitution, and it must share no code with the
e-graph it checks: that independence is the whole of its worth.

- **A test oracle.** Every pair the e-graph calls equal has an
  explanation the checker accepts, and a failure names the step that
  does not follow.
- **A debugger for unsound rules.** The explanation of a bendix
  `:conflict` is the chain of rules that produced it.
- **Not a judge of rules.** Rules are axioms here; it confirms that a
  derivation follows from them, never that one is true.

The hard part is every step that is not a plain rule instance:

- A guard or a computed right-hand side reads the e-graph, and must
  state its evidence: a constant fold is "`?a = 2` by this proof,
  `?b = 3` by that one, `2 + 3 = 5` by evaluation".
- An analysis merge needs a step checker that lives with the theory:
  "by ring normalization" is checked in bendix, by normalizing both
  terms and comparing.

## 3. Solvers

Nothing to add. `:make`, `:merge`, `:reconcile`, `:modify` and
`:analysis-state` are a theory solver's interface, and bendix's
polynomial analysis is a ring solver written to it. A prover's other
parts would also fit without touching the core: upward propositional
propagators are rewrite rules; downward ones are searchers, since
`apply-rule` takes `:class` and `:rhs` from each match as given;
constructor injectivity fits `:reconcile`; case splitting is keeping
the old e-graph.

## 4. A prover, by way of ansatz

Not alone. What makes a prover worth using is a trusted kernel and a
library of proved lemmas; without them it can say "equal" and no one
can check it. ansatz has both (Lean 4's kernel, Mathlib) and open
registries, so an adapter needs no change to ansatz.

- **Where it plugs in.** `a/register-tactic!` takes
  `(fn [ps args] ps')`. `a/register-simproc!` takes `(fn [st expr])`
  returning `{:expr simplified :proof eq-proof}`, which is saturate,
  extract the cheapest, and prove the result equal. Its own `grind`
  e-graph is not behind a protocol and is not ours to replace.
- **What it is.** A third library depending on both, JVM only,
  cromulent staying dependency-free. Three pieces: kernel expressions
  to tagged vectors and back (application spines as nodes; constants,
  free variables and literals as leaves; binders opaque at first);
  theorems `∀ xs, lhs = rhs` to rules; explanations to
  `Eq.trans`/`congrArg` terms.
- **What gates it.** Explanations, and nothing else from the core:
  ansatz accepts only proofs. There the kernel is the checker of
  section 2.
- **Caution.** [lean-egg](https://github.com/marcusrossel/lean-egg)
  was this adapter for Lean, with egg as the engine. It is no longer
  developed, and its README recommends Lean's `grind`, which ansatz
  already has. Kernel terms also carry what syntactic matching does
  not see: binders, type-class instance arguments, and terms the
  kernel holds equal by computation. The lean-egg paper
  (doi.org/10.1145/3776667) is where to start.
- **Where it would earn its place.** Cost-directed rewriting with a
  proof attached, which is optimization and not proving, and is the
  simproc's shape.

The same pieces serve bendix in the other direction: a result that
wants a kernel's assurance exports its explanation as a proof term.
That wants typed terms and a named lemma for every rule.

## 5. Open questions, and what building answered

Answered 2026-10-25, by the prototype:

- **Derivations, not proofs** (decided 2026-10-26). What `explain`
  returns is a proof in equational logic with the rules as axioms: it
  shows an equation follows from them, not that it is true, and its
  trusted steps are hypotheses. The code calls it a derivation, the
  word term rewriting uses, and the checker `cromulent.derivation`
  (`check`, `derives?`), so that "proof" stays for what a kernel
  checks (section 4). This note's sections 1 and 2 say "proof" as
  they were written.

- **A journal in the value.** `(egraph {:explain? true})` keeps
  `:journal {:births [...] :unions [...]}` in the e-graph, so it
  survives in timelines like everything else.
- **The birth table.** `add-node` conjes the node it stores; nothing
  else about it changed.
- **A lookup, not a buffer slot.** With a journal, the runner looks
  up where each side of a merging match occurs
  (`cromulent.pattern/witness`), the left-hand side in the snapshot
  the match was found in, and unions those two nodes. The flat buffer
  is untouched, and without a journal the apply path is as before.
- **A reason is any value**, `nil` when a caller gives none.
  `rebuild`'s unions say `:congruence`; the runner's carry the rule's
  name, both sides as patterns, the bindings and both witnesses, which
  is the whole of what the explanation needs. A computed right-hand
  side, a match's own and a searcher's are marked `:computed?`, and
  their steps are trusted.
- **Cost.** Nothing without a journal. With one, on the JVM, a few
  per cent on the AC-10 yardstick (2.73 s against 2.82 s) and nothing
  measurable on the egg rules row; on Jolt about a third on both
  (AC-10 5.9 s against 7.8 s, egg rules 0.88 s against 1.22 s). The
  Jolt cost is most likely the witness lookups the runner makes for
  every merging match, which build a node to look up at every
  position of both patterns; recording the matched node's id in the
  flat buffer would remove the left-hand side's half, if a journaled
  run on Jolt ever needs it. The bench has the rows, journal on and
  off. A saturated sum of eight atoms explains its input against its
  reverse in 8 ms on the JVM and 19 on Jolt.

Still open:

- bendix gives no reasons: its analysis merges arrive as `:asserted`
  steps with a nil reason. "By ring normalization" wants a step
  checker that lives in bendix, normalizing both sides.
- Proofs are unshared trees, written out in full; a proof as a DAG,
  or one shortened after the fact (Flatt et al. 2022), when one is
  too long to read.
- Generations (a term made by a rule in round r is not matched until
  later) as a scheduler beside backoff. Noticed in ansatz; unrelated
  to proofs.
