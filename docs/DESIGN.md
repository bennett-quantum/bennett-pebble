# Pebble — an optimising, pebbling circuit compiler for Bennett oracles

Design. 2026-11-10. Owner: this folder (`bennett-experiments`), independent of
the `bennett-workspace` process. Companion documents: `CORE.md` (definitions
and theorem statements), `THEORY.md` (proofs), `formal/` (Lean mechanisation),
`model/` (executable model and measurements).

Status of each claim is marked: **[proved]** analytic proof in THEORY,
**[mechanised]** checked in Lean, **[measured]** by the model,
**[designed]** specified here with an argument but not built, **[open]**.

---

## 0. The idea in one page

The ISA defines a lifted oracle by a reference construction (§3.6, §5.2): a
predicated step machine that, for each of B budget steps, dispatches *every*
row of the program under a superposed program counter and keeps a frame
holding the old pc, a flag, a successor and every displaced value; then
commits and runs the whole thing backwards. That construction is a
*definition of meaning*. As a circuit it multiplies five independent wastes:

| Waste | Reference cost | Why it is not needed |
|---|---|---|
| Dispatch | every one of n rows, every step | at step t only the rows reachable at t can be active |
| Frame | old pc + flag + succ + all displaced bits, every step | the information actually destroyed by a step is usually a few bits |
| Classical data | constants and classical memory become wires and gates | a wire whose content does not depend on the superposed input need not exist |
| Control | every gate under the predicate stack | in `U⁻¹ K U` only the commit `K` needs the inherited controls |
| Materialisation | B copies of the step held in memory | the circuit is a term with sharing and repetition; cost and emission are recursions over it |

Pebble removes all five, then treats what is left — the history that makes an
irreversible computation reversible — as a resource to be scheduled under a
qubit budget. The whole design follows from six principles.

1. **The target is `F_B`, not the step machine.** The ISA obliges an executor
   to produce the reference's final interface tuple on the domain D (§5.7,
   T6) and nothing else. The budget is a comparison on a row count, not a
   schedule (CORE Lemma 4.2).
2. **Staging.** Compilation is partial evaluation of the reference interpreter
   with respect to everything classical at launch: the object, the budget,
   the classical arguments, the memory image. Only data that depends on the
   superposed input becomes wires (CORE Lemma 2.4).
3. **Garbage is information.** A step must retain exactly enough to be
   inverted. The compiler minimises that *residue* by choosing in-place and
   relabelling rules; the full displaced value is only the fallback
   (CORE §3).
4. **History is a game.** After 1–3 the computation is a chain of steps, each
   leaving a small residue, over a state that can be checkpointed. Keeping
   residues (Bennett 1973) and keeping checkpoints with recomputation
   (Bennett 1989) are the two moves of one game played under the qubit
   budget (CORE §6).
5. **The optimiser is untrusted.** A compute that is a composition of
   certified *sound moves* ending in the right result is correct, whatever
   chose the moves (CORE Theorem 2.5); a schedule is validated by replaying
   it in a small rule calculus. Search heuristics, exact solvers and learned
   policies are all outside the trusted base.
6. **Nothing is materialised.** The output is a hierarchical term with shared
   definitions and repetition. Its size is `O(|program| + log B)`; resources
   are computed by structural recursion; flat gates are streamed
   (CORE Theorem 7.2).

Collatz is the smoke test for this. The design load is the Linux kernel:
billions of steps, megabytes of state that is almost entirely classical,
calls, memory, indirect control. Section 6 says what holds at that scale and
what does not yet.

## 1. Where it sits

```
  ISA object (reference body) ──┐
  budget tuple, classical args ─┤                       ┌─▶ hierarchical circuit (term DAG)
  memory image, region bindings ┼─▶  Pebble  ──────────┼─▶ resource vector (exact, by recursion)
  target description, objective ┤   (library, Rust)     ├─▶ schedule + replayable derivation
  peak-qubit capacity per class ┘                       └─▶ certificate: claims, bounds, gap
```

- **Caller.** The VM at region launch (all classical data is known then), and
  the ahead-of-time specialiser `bennett-circuits` (the same call with the
  classical data that is known ahead of time). One implementation.
- **ISA hooks used.** §5.7 executor transformations (extensional agreement,
  T6); §17 item 18 pebbled realisations bound as an expansion library (§11);
  §9.4 frame descriptor reporting realised history. Nothing in the ISA has to
  change for the permutation-tier design. Measurement-based uncomputation
  (§8 below) needs the deferred §17 item 6.
- **What it replaces.** The literal expansion in `bennett-circuits`. It does
  not replace the reference interpreter, which remains the definition of
  `F_B` and the oracle the compiler is tested against.
- **Trust.** Trusted: the reference interpreter, the gadget specifications
  (each a small permutation with an exhaustively checked or structurally
  proved transfer function), the replay checker, the cost recursion.
  Untrusted: everything that makes a choice.

## 2. Semantic foundation

All of this is in CORE; the summary is what a reader needs to follow the
pipeline.

**Symbolic states.** During the compute phase every scratch wire holds a
known Boolean function of the environment `x` (the superposed inputs). A
circuit is a *sound move* `κ ⟶ κ′` if it maps the encoding of `κ` to the
encoding of `κ′` for every `x`. Sound moves compose, invert and frame.
[mechanised]

**Oracle contract.** If `U` is any sound move from "inputs only" to a state
holding `payload(F_B(x))` and `code(F_B(x))` in two bundles, then
`V = U⁻¹ K U` with `K` the two CNOT fans into `tgt` and `fr` is the §5.2
oracle on all of D, is an involution there, and its controlled form controls
only `K`. Garbage left by `U` is irrelevant; cleanliness matters only for
wires `U` reuses. [mechanised]

**Rule calculus.** Named values on wire bundles, with rules Eval (XOR-form,
self-inverse), Copy, InPlace (bijective update with a residue), Relabel
(zero gates) and Guard. The classical reversible pebble game is the Eval-only
fragment. [mechanised]

**Budget.** With `N(x)` the number of rows of the unbounded run and `out(x)`
its outcome, `F_B(x)` is `out(x)` when `N(x) ≤ B` and the step-budget fault
otherwise. The compiled machine may group rows arbitrarily and overrun B, as
long as it knows `N(x)` at the halt. [proved; scope conditions in THEORY]

## 3. Pipeline

Six stages. Each has a defined input and output, a correctness obligation
discharged by a CORE statement, and a stated complexity.

### Stage A — Specialise (online partial evaluation)

*In:* reference body, classical data. *Out:* a residual program over
**symbolic bit-vectors**, where every bit is `0`, `1`, or a reference to a
wire (possibly negated).

The specialiser is an abstract interpreter of the reference semantics whose
abstract values are binding times with content: `const(c)` or `wire`. A row
whose operands are constant executes classically and emits nothing (it still
counts one row). A branch on a constant predicate is classical control: the
pc stays classical and there is no dispatch at all. A branch on a wire forks.
Shifts, masks by constants, extensions and truncations are relabelings of
bits. Local memory starts as its classical image: a load at a classical
address from a classical cell is a constant, so state that is only ever
addressed classically costs no qubits. That is the limit of the claim: a load
at a *superposed* address needs a lookup circuit over the address's value
set, and a store at a superposed address turns every cell it may touch into
wires.

Forked paths are explored in **layers** and merged when they meet at the same
merge key (pc and call context) in the same layer. Merging joins bit by bit:
equal constants stay constant; anything else becomes a wire defined by the
path predicates. This is state merging as in symbolic execution, except that
the output is a circuit.

Termination and cost: the abstract state (reachable set, binding-time map,
row-count set) is compared across layers; when a layer repeats an earlier one
up to renaming, the steady state is emitted as a repetition. If no repeat is
found within a window, constants are **widened** to wires, which is always
sound (it only costs gates) and forces convergence. Compile work is the
classical prefix (which is simply running the program), plus the transient to
the abstract fixed point, plus `O(log B)` for the schedule. [designed; the
model implements constant folding, bit aliasing and time-indexed
reachability, not the general merge-and-widen loop]

*Obligation:* Lemma 2.4 (deleting gates controlled on constant-0 wires, and
controls that are constant-1, preserves soundness).

### Stage B — Guarded block machine

*Out:* a GBM (CORE §5): superblocks with straight-line bodies, exits, a row
weight per exit path, and a state consisting only of values live across block
boundaries.

- Rows are merged into superblocks; lprocs with classically known call
  context are inlined, keeping their `lift.call`/`lift.ret` rows in the weight
  and deciding their depth and stack faults classically (§3.7). Recursion
  with superposed depth keeps an explicit stack; the merge key carries the
  call context while contexts stay few, and widens the frame pointer to a
  wire when they do not.
- **Time-indexed reachability.** `Reach_t` is computed classically; step `t`
  dispatches only `Reach_t`, and `Pred_t` gives each block's possible
  predecessors at that step.
- **Row counter.** `c` accumulates row weights. If at every reachable
  `(t, b)` it has a single value it is classical and over-budget transitions
  are pruned at compile time; otherwise it is a `⌈log₂⌉`-width state variable
  updated in place by constants, with no residue. Faults inside a block
  freeze `c` at the faulting row.
- **Synchronisation is a choice.** When two paths rejoin out of phase, every
  later block becomes reachable at two phases and is paid for twice per step.
  Inserting weight-0 wait blocks at a join re-aligns the paths (this is the
  Quantum Control Machine synchronisation condition, used as an optimisation
  instead of a requirement). Padding a loop to a bound `K` is the same move.
  The compiler chooses where to synchronise by comparing
  `Σ_t Σ_{b ∈ Reach_t} cost(b)` with and without the waits. Structured `if`
  and bounded `loop` are what this choice produces on reducible code; nothing
  is lost on irreducible code. [designed; the choice problem is open, §9]

*Obligation:* Lemma 5.2 (each transformation preserves simulation), Theorem
5.3 (the committed pair equals `F_B`).

### Stage C — Data path: the residue calculus

*Out:* for each block, a derivation in the rule calculus taking the old state
to the new state plus a residue.

For each state variable a block overwrites, the compiler looks at the
expression for the new value in terms of the old one. If it is a chain of
in-place-capable operations rooted at the variable's own old value, with all
other operands stable for the duration, it is applied in place and the
residue is the union of the chain's residues (CORE Definition 3.4). Otherwise
the new value is evaluated out of place and the old value is the residue —
exactly the reference's displaced slot.

Rules that matter in practice:

- `x ± y`, `x ⊕ y`, `x ± c`, rotations, `¬x`: no residue.
- `x · c` with `c` odd: no residue. Realised either as a carry sweep for
  `c = 2^k + 1` (`x += x ≪ k`: one adder's worth of Toffolis, descending
  clean-up so each addend bit is still intact when used) or, for general odd
  `c`, as controlled constant additions into the suffix from the top bit
  down.
- `x ≫ c`: the residue is the `c` bits shifted out; the shift is a
  relabeling.
- `select(p, e₁(x), e₂(x))` with both arms in place: one bit `p`, plus each
  arm's residue under its guard. A residue bit that the guard forces to 0 is
  clean and is dropped: after testing `x` even, the bit shifted out by
  `x ≫ 1` is 0.
- Stores to memory at a classical address: exchange, residue the old cell.

The Collatz step `x ← even(x) ? x ≫ 1 : 3x + 1` is the illustration: the
reference frame keeps the full old `x`, the old counter, the old pc, a flag
and a successor; the residue calculus keeps one bit, the parity. That is the
information-theoretic content of the step.

**Block-internal temporaries** are a pebble game on the block's DAG. For
small blocks it is solved exactly (shortest path over pebble configurations,
with the search itself as the optimality certificate); for large blocks,
Bennett-style compute/uncompute with eager cleanup, with the bound from the
trivial lower bound reported as the gap.

**Cleanup laziness is a scheduling decision.** Uncomputing a block's
temporaries inside the step doubles the step's cost and keeps the residue
small; leaving them makes them residue. Both are legal; with space to spare
the lazy form halves the total gate count. The choice is one more parameter
of the chain game (a smaller `a`, a larger `r`), not a code-generation
convention. [designed]

**Arithmetic selection.** Each operator has several gadgets (ripple versus
carry-save versus lookahead adders; multiplication by shift-add versus
in-place sweeps; comparators), each with a specification (a sound move) and a
cost vector as a function of width in the target's resources. Selection is by
the objective. Gadgets come with certificates from `bennett-arith`; the
compiler only composes them.

*Obligation:* Theorem 3.2, entry by entry of the residue table.

### Stage D — Control path: predecessor-rank frames

*Out:* the step circuit `S_t`, a sound move `{σ_t} ⟶ {σ_{t+1}, ρ_t}`.

The reference frame stores the old pc, a flag and a successor (2P + 1 bits).
What a step actually destroys about control is *which incoming edge* led to
the new pc. Construction 5.5 computes one-hot flags for the edge taken, writes
the new pc and a **predecessor rank** of `⌈log₂ max |Pred_t|⌉` bits under
them, then erases the old pc, the edge flags and the dispatch flags by
decoding (new pc, rank). On straight-line and loop-interior steps the rank is
zero bits wide. (The first version of this construction erased raw exit
predicates from the rank; the theory track refuted that — an inactive block's
predicate is not a function of the edge taken — and the one-hot edge flags
are the repair. Predicate helpers are cleaned from the old data before it is
overwritten.) [proved: THEORY A.9]

Refinements:

- **Decode by unary iteration.** The dispatch flags `[pc = b]` for all
  reachable `b` are produced by a binary-tree decode costing about one
  Toffoli per reachable block per step, rather than a comparator each.
- **Halt-time counter.** HALT has two predecessors forever after (the exit
  and itself), which costs one rank bit per step. A `⌈log₂ T⌉`-bit counter of
  the halting step, incremented in place while not halted, makes the idle
  self-loop distinguishable by comparing the counter with the classical step
  index. The rank bit disappears, and a loop whose body is injective then
  needs `O(log T)` bits of history in total instead of `T`. This generalises
  the identity-idle step of §17 item 17. [designed]

*Obligation:* Lemma 5.6.

### Stage E — History: the chain game

*Out:* a schedule — a legal play of the chain game — within the qubit
capacity, minimising the target objective.

After A–D the compute is a chain of `T` steps. Position `j` has a state of
`m_j` live non-constant bits; step `j` costs `a_j` and leaves `r_j` residue
bits; copying the state costs `m_j` CNOTs and no Toffolis. A configuration is
a set of state copies (tokens) at positions and a set of retained residues.
A token advances by leaving a residue, retreats by consuming one, and can be
duplicated. The compute phase must reach a token at `T` without exceeding the
capacity (CORE Definition 6.1).

The two classical strategies are the game's corners: one token and all
residues (space `m + rT`, time `T`); tokens only with a residue held for one
step at a time (Bennett 1989; space `O(m log T)`, time `T^{log₂ 3}`, or
Knill's optimal trade-off). The mixed regime — runs of history of length `ℓ`
between checkpoints — is where a compiler with small residues lives, because
`r ≪ m` makes history cheap *per step* and checkpoints cheap *per segment*.
What is established (THEORY Part B):

- An exact optimum for small instances by shortest-path search, the ground
  truth. [proved]
- A **nested class** of schedules — history leaves joined by *bridges* (run a
  sub-schedule forward, copy its endpoint, run it backward) — with an interval
  recurrence that is exactly optimal within the class, for uniform and
  non-uniform chains. [proved] It equals the unrestricted optimum on every
  one of the 650 instances searched; whether it always does is open.
- Compact schedules: balanced recursion with fan-out `κ`, depth `L`, leaves of
  length `ℓ`: `T = ℓκ^L`, compute cost `aℓ(2κ−1)^L`, peak
  `m(1 + L(κ−1)) + ℓr`, described by `O(L)` records. [proved for κ = 2;
  general κ computed in `theory/kary_frontier.py`, within 1.53× of the exact
  nested optimum on the 85 small instances compared]
- A lower bound `a·max(T, 2T − ⌊(S−m)/r⌋)` that certifies the gap of any
  schedule. It is loose; tightening it is open. [proved]

The fan-out matters enormously. Binary recursion is the textbook picture and
is the *minimum-space* corner; a compiler with qubits to spare should use wide
fan-out and long leaves. §6 has the numbers.

Three things extend the uniform game to real programs. [designed]

- **Natural checkpoints.** `m_j` varies along the chain: at a function
  return the callee's locals are dead, at a loop back-edge only the loop
  state is live. The non-uniform program places tokens where state is small.
- **Per-call cleanup is one strategy, and a bad one.** "Compute the callee,
  copy the result, uncompute the callee" at every call doubles cost per
  level of nesting, `2^depth` overall. In the game it is the play that puts a
  token at every return and retreats immediately. The game finds the plays
  between that and full history.
- **Delta checkpoints.** A token need only hold the bits written during the
  span in which it is retained; the rest is shared with the working copy.
  Short-lived tokens deep in the recursion are small. This makes a token's
  cost depend on its live span, which changes the dynamic program; the
  analysis is open (§9).

*Obligation:* Theorem 6.2, plus replay by the checker.

### Stage F — Commit, lowering, emission

- **Commit.** Compare `c ≤ B` if `c` is quantum; XOR payload and code into
  `tgt` and `fr` under the inherited control context; this is the only place
  the context appears. Then the inverse of the compute.
- **Lowering.** MCX and the gadgets are lowered to the target alphabet by the
  target's schemes (§8.3). Retained residues and checkpoints are a large pool
  of idle wires: they are offered as **dirty ancillae** to MCX and
  incrementer decompositions under the borrow discipline of §5.6, so that
  pebbling's idle space pays for cheaper gates.
- **Emission.** The term DAG is written as the hierarchical circuit object;
  resources come from the recursion of Theorem 7.2; flat exporters stream.
  For §17 item 18 the same traversal lists every allocation, copy, forward
  evaluation, inverse evaluation and release with distinct ordinals, as a
  generator rather than a stored list.

## 4. Cost model and what "optimal" means

The target supplies a resource vector and either weights or a lexicographic
order (§8.2). Every term of the hierarchy carries a cost record: gate counts
by native gate, makespan, peak live wires per class, and wire-time per class.
Records compose by sequence (counts add, peaks take the maximum over a common
base), call, repetition and adjoint; the recursion is exact, not an estimate.
[measured against simulation in the model]

Claims of quality follow the north star's rule:

- **Exact** for the small sub-problems solved by exhaustive search (a block's
  internal pebbling, a chain short enough to search): the search is the
  certificate.
- **Optimal within a named class** where THEORY proves it (nested strategies
  of the chain game).
- **Bounded gap** otherwise: the schedule's cost against a proven lower
  bound, both in the certificate. No minimality claim is made without one of
  the first two (and cert 0.9 does not admit minimality claims at all, §1.3;
  the gap is reported as data).

## 5. ISA conformance

| ISA obligation | How Pebble meets it |
|---|---|
| §5.2 contract on D | Theorem 2.5, for any legal schedule |
| §5.7 / T6 extensional agreement | Lemma 5.2 + Theorem 5.3: the GBM simulates the reference body; the committed pair is `F_B` |
| §17 item 18 | **this is the hook the realisation uses.** The schedule is bound as an expansion library; operations are enumerated with distinct ordinals by the emitter, every replay included and charged; the full-domain argument is the replayed derivation plus Theorem 2.5 |
| §6.2 `reverse` cleanup | *not claimed for the oracle's interior.* At the level of the schedule every cleanup is an exact adjoint (`Ret` of `Adv`, `Undup` of `Dup`, the uncompute half of the compute half). Inside a step, though, erasing the old value of an in-place update or the old pc from the rank is an algebraic erasure from updated operands, not the adjoint of the value's computing sequence on its original versions. THEORY A.10 is explicit that circuit soundness and a §6 annotation are separate conclusions. §6 governs producer-written structured regions; a compressed certificate format for algebraic erasure is an open item (§9) |
| §6.4 unitary cleanup only | yes in the core; ghost pebbles are a separate, non-conformant extension |
| §9.4 frame descriptor | realised history = the schedule's peak retained residues and tokens, as expressions in the inherited control count (constant: controls touch only `K`) |
| Faults | the row counter and Theorem 5.3 give the reference's fault code, including the first fault in sequential order and the step-budget fault |

Where the proofs found CORE or the ISA text to need a scope condition, it is
listed at the top of THEORY and carried into §7 here.

## 6. Kernel scale

What the principles buy at `B = 10⁹`, and where the design is still thin.

**The price of a billion reversible steps.** For a uniform chain of
`T = 10⁹` steps with state width `m` and residue `r` bits per step, the best
balanced `κ`-ary schedule under a qubit cap `S` costs the following multiple
of the irreversible step count (2.0 is the floor: compute once, uncompute
once). Copies are not priced; evaluator workspace is extra. These are legal
schedules, not proven optima. [computed: `theory/kary_frontier.py`]

| `m` | `r` | cap `S` | depth `L` | fan-out `κ` | leaf `ℓ` | replay factor |
|---:|---:|---:|---:|---:|---:|---:|
| 10³ | 1 | 3·10⁴ | 11 | 3 | 5,646 | 551 |
| 10³ | 1 | 10⁵ | 4 | 12 | 48,226 | 27 |
| 10³ | 1 | 3·10⁵ | 2 | 95 | 110,804 | 7.9 |
| 10³ | 1 | 3·10⁶ | 1 | 382 | 2.6·10⁶ | 4.0 |
| 10³ | 100 | 10⁵ | 6 | 13 | 208 | 101 |
| 10³ | 100 | 10⁶ | 3 | 49 | 8,500 | 15.5 |
| 10³ | 100 | 3·10⁶ | 2 | 196 | 26,031 | 8.0 |
| 10⁵ | 10 | 10⁷ | 3 | 12 | 578,704 | 14.1 |
| 10⁵ | 10 | 10⁸ | 1 | 113 | 8.8·10⁶ | 4.0 |
| 10⁷ | 100 | 10⁹ | 2 | 12 | 6.9·10⁶ | 7.4 |

Three readings. First, the residue width is the lever: at a fixed cap, going
from `r = 100` to `r = 1` is worth a factor of several in gates, which is why
Stage C matters more than any scheduling cleverness. Second, a few hundred
state-widths of space buys a billion steps for under 8× the irreversible gate
count; at minimum space the same chain costs hundreds to tens of thousands of
times more (the binary schedules of THEORY B.7). Third, the state width `m`
here is the *proved live non-constant width*, which for a kernel workload
nobody has yet measured; the table says what the answer would cost, not what
`m` and `r` are.

**What holds.**

- *The schedule does not scale with the budget.* The schedule for a uniform
  chain of `10⁹` steps is a handful of records, planned in milliseconds.
  The classical prefix is executed, not compiled. Whether the *superposed*
  part compiles in time independent of the budget depends on the program
  having a regular reachability and residue summary; step-by-step
  reachability is itself linear in the horizon (THEORY C.1).
- *Classically addressed classical state is free.* Only the footprint that
  depends on the superposed input becomes wires. For the fuzzing rung
  (snapshot fixed, syscall arguments superposed) that is the taint closure of
  the arguments, not the kernel image — provided addresses stay classical.
- *History is small per step.* Residues are bits, not words, wherever the
  update is injective up to a few bits; the fallback is never worse than the
  reference frame.
- *Space is a dial.* The chain game turns any capacity above the minimum into
  the cheapest schedule for it, and reports the gap to the lower bound.
- *The description is small.* `O(|program| + log B)` term nodes; nothing is
  held per step.

**What is thin.**

- *Dispatch width.* Each step pays for every block reachable at that step.
  When superposed paths drift out of phase the reachable set grows towards
  the whole tainted region and the "budget × blocks" cost returns.
  Synchronisation (Stage B) is the lever; choosing where to synchronise is
  an optimisation problem this design states and does not solve.
- *Superposed addresses.* A load or store whose address is a wire costs a
  multiplexer over the address's value set. Value-set analysis in Stage A
  bounds it; pointer-heavy tainted code is expensive and nothing here changes
  that short of target QRAM.
- *Merging policy.* Which paths to merge, and when widening is cheaper than
  exploring, decide whether Stage A produces a small machine or a large one.
  The policy is heuristic.
- *Delta checkpoints and non-uniform chains* at this length need the
  hierarchical dynamic program, which is specified but not built.
- *Idle-wire borrowing* interacts with scheduling (a borrowed wire must be
  idle for the borrow's whole duration) and is not yet in the cost recursion.
- *The reference stack is monotonic.* §3.7 never pops the lproc stack (records
  are history). A realisation that reuses stack storage needs its own
  simulation proof; until then deep call chains carry their records in `m`.
- *Nobody has measured `m` and `r` for a real workload.* Every kernel-scale
  statement here is conditional on them.

## 7. Results

Status at wind-up, 2026-11-10. Full detail: `model/RESULTS.md`, `docs/THEORY.md`,
`formal/README.md`; what is and is not checked: `HANDOFF.md`.

**Mechanised (Lean 4, `formal/`).** 65 theorems, no `sorry`, no added axioms:
the oracle contract from any sound compute (clean, dirty-scratch, controlled,
involution, garbage-independence), soundness of the five rules and of the
calculus, DAG strategy soundness, and chain-game legality ⇒ oracle. Rebuilt
from clean by the design owner.

**Proved on paper (`docs/THEORY.md`).** Soundness and ISA fidelity (Part A);
the mixed chain game: exact unrestricted search, exact recurrence within the
nested class, a lower bound, the balanced κ-ary family (Part B); ghost-pebble
correction rule (Part C). Twelve corrections to revision 1 of CORE, all folded
into CORE revision 2.

**Executable model (`model/`, Rust, std only).** Supports the memory-free
subset (layout-backed calls yes, lifted memory no). 39 unit tests pass.
Whole-oracle verification against the reference interpreter: 2,198
circuit/budget/control instances, all 8-bit inputs, all initial target/fault
values (symbolically), controlled and uncontrolled.

Residue per step (bits), before → after the residue calculus:

| Fixture | State | Residue | of which data |
|---|---|---|---|
| collatz | 206 → 118 | 206 → 4 | 1 |
| gcd | 70 → 62 | 70 → 3 | 0 |
| popcount | 78 → 62 | 78 → 4 | 1 |
| irreducible loop | 70 → 54 | 70 → 4 | 1 |

Collatz at B = 2048 (the legacy exporter was projected at ~972M gate nodes and
runs out of memory; units differ, so this is a rough comparison):

| Qubit cap | Peak qubits | Toffoli-equivalents | Checkpoints |
|---:|---:|---:|---:|
| unlimited | 387,188 | 4.9M | 0 |
| 18,097 | 14,629 | 19.7M | 0 |
| 10,545 | 8,785 | 88.4M | 3 |
| 7,241 | 6,676 | 168M | 8 |

Compile cost is flat in the budget: from B = 9 to B = 10⁹ the description grows
from 11,968 to 15,806–32,178 definitions, compile time stays at 0.2–0.35 s and
memory at 24–30 MiB. The B = 10⁹ circuits are priced by recursion over the
description, never expanded or simulated.

**Known gap between design and model.** The model's large-budget scheduler
only uses *binary* nesting (peak (2+d)m + ℓr, 2ℓ·3^d step runs). Stage E of
this design and `theory/kary_frontier.py` call for wide fan-out when space
allows. At B = 10⁹ with a 63,409-qubit cap the model runs each step ~3,900
times; a 60-ary, 3-level schedule should need ~8 (estimate from the theory
formulas, not measured). Closing this is the first model task.

**Not done.** Lifted memory and `sum_db`; an independent derivation checker for
data-path rewrites (the model relies on exhaustive fixture checks instead);
global optimality of the nested class (open); any measurement of state and
residue width on a real workload.

## 8. Extension: ghost pebbles (not ISA 0.9)

Measurement-based uncomputation removes a value by measuring it in the X
basis, leaving a phase `(−1)^{m·v(x)}` that is repaired later by recomputing
`v` and applying a classically controlled `Z`. In the game it is a third
status for a value: neither present nor absent, but owed. It lets a token be
dropped without the state it was computed from, which changes the trade-off
qualitatively (the spooky pebble game). It leaves the permutation tier: the
realisation is a channel, the certificate kind is the deferred §17 item 6,
and under a control context the fixup must be the controlled one. The rule,
its soundness as a channel and its controlled form are in THEORY Part C. It is
kept out of the core so that the core stays a theorem about permutations.

## 9. Open problems

1. **Synchronisation placement.** Minimise total dispatched cost over
   insertions of wait blocks, given the reachability dynamics. Likely hard in
   general; structured programs have an obvious optimum, and the interesting
   case is nearly-structured code.
2. **Span-dependent token cost.** The chain game with delta checkpoints.
3. **Joint optimisation of laziness, leaf length and arithmetic choice.** The
   three interact through `(a, r, m)`; today they would be chosen in
   sequence.
4. **Residue inference beyond the table.** Finding small residues is finding
   a small-garbage reversible embedding; the table is a set of syntactic
   rules. A semantic method (known-bits and value-range facts under path
   predicates, as in the parity example) would generalise it.
5. **Ghost pebbles under control**, with a certificate kind.
6. **Dirty borrowing inside the schedule.**
7. **Lower bounds for the block-internal pebble game** that are better than
   trivial and cheap enough to compute per block.
