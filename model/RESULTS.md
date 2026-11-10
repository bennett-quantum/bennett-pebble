# Pebble executable model — results

**Status.** M0–M6 have executable implementations for the supported memory-free subset. 39 unit tests pass. The final boundary harness records 2,198 passing circuit/budget/control instances, covering 3,464,495,104 interface basis assignments algebraically; no final failing instance was found. Collatz's optimized frame has **four bits: three predecessor-rank bits and one data-residue bit**. The exact chain solver and nested DP have largest observed additive gap **0** on 374 recorded instances.

**Limits of this result.** Large-budget gate/qubit figures come from the actual hierarchical circuit's cost recursion; billion-step circuits were not flat-emitted or simulated. The large-chain planner chooses checked regular nested strategies and does not claim global optimality or the exact large-T optimum of the small-instance DP. This model does not compile Linux or SQLite. Lifted memory and the two stretch goals are unimplemented. The parser reads executable bodies and relevant layout fields, and does not authenticate JSON envelopes or closure hashes. Further scope limits and deviations from CORE are listed below.

## Milestones and evidence

| Milestone | Delivered | Verification and limits |
|---|---|---|
| M0 | Text parser, arbitrary-width bit vectors, reference interpreter, fixed classical integer/ptr/f64 arguments, short-form calls/returns, heap/stack/depth tuple validation | All 256 inc8 inputs; all 255 terminating Collatz inputs at their individual before/at/after boundary; input zero under finite budgets; recursive capture/restore; monotonic-stack call loop; wide fault literals and effective cause 0→4. Memory, token forwarding, nonempty lproc forwarding headers, indirect jumps, and unlisted rows are rejected explicitly. |
| M1 | Shared gate/sequence/call/adjoint/control/repetition/allocation IR; direct basis simulator; exact native cost recursion; streaming flat emitter; shared-description writer | XOR evaluators exhaust every input and arbitrary output at widths 1–3; in-place arithmetic exhausts widths 1–4. At width 1, evaluators also enumerate dirty physical scratch and check scratch preservation and inverse permutation. Controlled forms, select/casts, and an odd multiplier above 64 bits are tested. Scope release checks cleanliness. |
| M2 | Context inlining, weighted superblocks, liveness, slot coalescing, finite-prefix/periodic reachability, static count analysis, coherent counter fallback | Emitted steps use the time-indexed reachable blocks. HALT is additionally included because an over-budget block is allowed to halt early with code 1. The static counter analysis is sufficient, not complete: it proves absolute block-entry counts and otherwise uses a coherent counter. The unbalanced diamond loop exercises that fallback. |
| M3 | Full-old-state history baseline and compute/commit/uncompute oracle; inherited control on commit only | Whole final tuples are compared with M0: input, arbitrary initial target/fault, control, and every released scratch wire. Both uncontrolled and controlled forms are covered. |
| M4 | Constant/alias bit views, rematerialization, inverse arithmetic rules, guarded select chains, known-zero discarded bits, old-value fallback | Full boundary verification is repeated for both residue implementations. Odd multiplication inverse has a Boolean-evaluator implementation and an implementation using the adjoint of the in-place multiplier. Automatic odd-multiply inversion currently uses the optimized rule up to width 64; larger cases retain the old value. |
| M5 | Exact Dijkstra, uniform/nonuniform nested DP, explicit legal-move replay, compressed regular strategy checker, actual checkpointed circuit lowering | Small DP strategies are independently replayed. Large strategies have an inductively checked leaf/split certificate. Small circuits force multiple checkpoint levels. The compact large strategy is a named heuristic family, not an optimality theorem. |
| M6 | Seven fixtures × six B values × unlimited/four fixed peak budgets; actual selected circuit costs; fresh-process compile time and RSS | 210 measured compilation records. Quotas are fixed across B for each fixture. Costs are exact under the stated gate/decomposition model. Correctness simulation has the separately documented finite domains. |

The new measured programs are subtractive gcd, popcount, an unbalanced diamond in a loop, an irreducible two-entry loop, and reachable `lift.faultif`. `inc8` is an additional baseline. `countdown`, `call_loop`, and `add_classical` are extra semantic regression fixtures. New fixtures are body-level model inputs; their envelopes are not authenticated by a full ISA loader.

## Corrections and interpretations of CORE

1. **Theorem 5.3 has an off-by-one in its sufficient horizon condition.** A weight-one self-loop, after B block steps, has c=B and is not halted. Thus “H=B always works” is false with the printed condition c>B. Replacing that condition by c≥B makes the stated sufficient horizon valid: another positive-weight block cannot halt within budget. The commit formula itself is sound at H=B. A unit test contains this counterexample. The model compares row counts and can halt an over-budget block immediately with `(0,1)`; it does not change F_B.
2. **Definition 3.1 needs bit views to express Lemma 2.4 and the advertised relabelings.** A width-64 zero-extension of eight wires cannot be a tuple of 64 distinct existing physical wires with 56 constant wires absent. The executable representation uses `Const(bool) | Wire(id)` entries, allowing repeated aliases, while owned physical placements remain disjoint. Mutable state slots may share storage only when their live ranges do not interfere. This is a representation extension, not a claim that a physical wire stores two different values.
3. **In-place `x += x << k` requires k>0.** At k=0 it is multiplication by 2 modulo 2^n and is not injective. The gadget rejects k=0; general compilation can retain the old value. The shift-residue rule clamps a discarded-bit count to the operand width.
4. **The word “memoryless” is narrower in ISA §7.2 than in the task's examples.** An object without layout has no lprocs or calls and requires heap=stack=depth=0. Collatz has layout and a call. The implemented subset is therefore *no lifted memory access*, with layout-backed calls supported. This preserves the requested Collatz semantics.
5. **Rank and counter analysis are conservative.** Rank uses a fixed predecessor table, including budget-to-HALT edges, rather than minimizing the rank width separately at every time phase. Counter analysis does not attempt the strongest affine `(t,block)` proof. These choices can cost qubits; they do not alter the oracle function.
6. **Theorem 7.2 is used for well-formed wire maps and fresh inherited controls.** The constructors require injective call maps and a control disjoint from the body's support. This excludes overlapping control contexts whose effective controls would need set deduplication. Native physical peak allocation is priced exactly; reported decomposed peak additionally reserves a shared clean MCX ladder pool for the whole oracle. This is a stated allocation policy, not a minimum-ancilla theorem.
7. **Flat output necessarily grows with expanded gate count.** The shared description and its pricing do not. The flat emitter streams that output with lazy wire maps and no vector proportional to an allocation count. A test emits a scope of 10^9 declared wires and two gates without materializing those wires.

CORE itself was not edited: this task authorizes writes only in `model/` and `fixtures/`.

## Reference semantics and boundaries

The interpreter charges one executed source row, including call, return, branch, jump, fault, and retval. It captures call arguments before clearing/pushing the selected callee file; return captures its result before restoring the caller's view. **sp remains monotonic on return.** The depth and stack flags compare prospective values without bit-vector wrap. Fault code literals have the full declared fault width, and literal zero records code 4. Arithmetic wraps at its declared width. Every shift amount ≥ operand width, including `ashr`, produces zero.

Verified against the real fixtures:

- inc8 succeeds at B≥3 with `(x+1 mod 256,0)`; B≤2 yields `(0,1)`.
- Collatz under `(heap,stack,depth)=(0,32,32)` needs 9 rows for x=1; an input taking j loop iterations needs `10+18j` rows. All terminating inputs 1–255 were checked at N−1, N, N+1 in the reference tests.
- Collatz under `(0,27,1)` reports code 3 on the first executed row for B≥1, and code 1 for B=0. The lproc record is 28 cells.
- The recursive countdown restores parent locations, including an operand used after the recursive call. The call-loop fixture checks stack exhaustion after returned calls, even though depth has fallen again.

`verification-boundaries.csv` takes every halt/fault row count observed for x=0…255 with reference cap 4096, includes N−1/N/N+1, and adds explicit small budgets. All successful/faulting runs of the seven measured fixtures halt within that cap. Collatz input zero does not terminate; it remains included in every circuit comparison. Both controls and all target/fault initial values are covered at each logged boundary budget. The large-B cost grid is a different experiment and is not labeled as simulation.

## Whole-tuple verification method

The ordinary simulator executes the hierarchy without flattening and checks zero scratch at every scope release. The sampled harness uses several nonzero targets/fault registers and compares every final interface bit with the reference. Its uncached gate counter is cross-checked with structural costs.

The stronger harness carries truth tables in environment/control bits and independent affine symbols for every initial target/fault bit. Gate execution checks that no affine target/fault symbol is ever used as a control. Consequently this representation is exact for these circuits, and a successful run covers **all** initial target/fault assignments. For an 8-bit input, 8-bit target and 4-bit fault register, one uncontrolled log entry covers 1,048,576 basis assignments; a controlled entry covers 2,097,152. Scratch must have zero truth table and zero affine mask before release. Calls are memoized by their complete mapped truth state. The inverse cache uses the exact inverse gate sequence; smaller uncached simulations provide a separate check.

This is exhaustive for the listed finite environment/control domains and symbolic target/fault values. It is not a proof for arbitrary programs or arbitrary widths. The general sampled harness permits at most 12 input bits; the truth/affine fast path permits at most 8 input bits and 128 combined target/fault bits. Fixed classical argument tests use four i8 bindings and representative ptr/f64 bit patterns; arguments are not counted as quantum inputs.

During development the harness rejected an inverse that assumed dead slots were zero after a branch while the forward machine had retained the union of successor values (e.g. x=1, B=8). A second failure at x=2, B=28 exposed a dropped branch value whose equality constraint had to be used in inversion. The final implementation canonicalizes the chosen successor's live slots and reconstructs equality-constrained values; both cases are retained as regressions. These were real failing instances, and no failed record is being presented as a verified result.

## Residues and state

The following widths are computed from the generated implementations at B=10^9. For acyclic programs, a structural all-HALT horizon stages the budget and shortens the schedule. “State” includes protocol fields; “data residue” excludes rank.

| Fixture | State before | State after | Residue before | Residue after | Rank | Data residue |
|---|---|---|---|---|---|---|
| inc8 | 13 | 13 | 13 | 1 | 1 | 0 |
| collatz | 206 | 118 | 206 | 4 | 3 | 1 |
| gcd | 70 | 62 | 70 | 3 | 3 | 0 |
| popcount | 78 | 62 | 78 | 4 | 3 | 1 |
| diamond | 78 | 62 | 78 | 4 | 3 | 1 |
| irreducible | 70 | 54 | 70 | 4 | 3 | 1 |
| faultif | 14 | 14 | 14 | 2 | 2 | 0 |

For Collatz, live-range coalescing puts the loop data in 72 physical slots. The old-value baseline retains the whole union state per step. The optimized rule inverts increment and odd multiplication, records the parity choice, and uses the even guard to reconstruct the shifted-out low bit as zero. Counter increments are inverted using the recovered predecessor. Thus the actual frame is four bits, including one data bit. No fixture name occurs in these rules.

Uniform state encoding still reserves protocol bits that may be constant in some phases. More complete phase-specific layouts could reduce the qubit count further. Unknown or unsupported inverse patterns use old-value residue. The optimizer also keeps the full-history candidate because it can have fewer gates when space is abundant.

## Chain game and compact scheduling

Dijkstra searches complete configurations `(multiset of token positions, retained residue set)` with no nesting assumption. It reports shortest paths only after removing a minimum-cost goal from the queue; those paths are replayed independently. Bounds are T≤16, positive token widths, at most 254 tokens, and a configurable state limit. A state-limit error makes no optimality claim.

The nested DP stores `R(i,j,s)` for reaching j and `C(i,j,s)` for keeping i while cleanly producing j. A leaf C advances, copies j, and reverses. Its cost is `2*sum(a)+k_j`; its peak includes the retained endpoint during reversal. A clean split at h uses independently chosen forward-left, right, and inverse-left strategies:

```
C(i,j,s) = min_h C(i,h,s) + C(h,j,s-m_i) + C(i,h,s-m_j)
R(i,j,s) = min_h C(i,h,s) + R(h,j,s-m_i)
```

Feasible direct/leaf alternatives are also minimized. Position-dependent state widths, residue widths, step prices and copy prices are used throughout. This is exact within this explicitly defined nested grammar, with O(T^2 S) memo states and O(T^3 S) worst-case time for integer S. It is not a proof that every optimal chain play is nested.

The recorded comparison grid has 342 uniform instances (T=1…6, m=1…2, r=0…2, S=m…10, a=2, k=1) and 32 nonuniform instances at T=5. The largest observed gap is 0 and the number of nested reachability misses is 0. Exact per-instance costs and explored-state counts are in `chain.csv`.

For large T, a regular strategy stores leaf length ℓ and level count d, pads to `ℓ*2^d≥T`, and has clean-compute peak `(2+d)m+ℓr`, `2ℓ*3^d` step moves and `3^d` copies. A separate checker recomputes these quantities and the legal leaf/split invariants. The circuit reuses definitions and maps a finite-prefix/periodic step family through each segment. For a fixed program the number of schedule definitions is O(log T). The actual nonuniform gate costs are then recomputed from the emitted term DAG. The selection score uses a maximum step price; it need not choose the best nonuniform schedule.

The separate T=10^9 planning/checking benchmark ran 10,000 iterations in 9,643 µs: mean 964 ns per plan plus check. It selected leaf 954, levels 20, padded length 1,000,341,504, and checked peak 3,492 for m=72, r=2, S=4096. This is a scalar-descriptor benchmark, separate from complete compiler timings. See `uniform-1e9.json`.

`best` compares full-old-state, Boolean-inverse residue, and compact in-place-inverse residue candidates, using structural Toffoli count, native gate count, and peak as the ordering. Each candidate uses direct history when it fits and otherwise a checked regular schedule. Failure to find a strategy in these families does not prove global infeasibility.

## Measurement conventions

- **C: computed by structural recursion.** Native gate histogram, expanded native gate count, native peak live allocation and MCX-decomposed qubits/Toffoli count. No expanded gate list is built. Histogram key k means k positive controls: 0=X, 1=CX, 2=CCX, ≥3=MCX.
- **W: measured.** `compile_us` covers parsing, all candidate construction, scheduling and cost selection in a fresh release-mode subprocess. `peak_rss_kib` is that process's Linux `VmHWM`, including runtime/image overhead, not a heap-only delta. Parent process startup is excluded from compile time.
- **V: verified by simulation.** The separate verification CSVs identify finite circuit/budget/control instances. The cost grid's `simulation` field is false.
- **P: supplied projection.** The parent project's legacy-generator analysis projects `G(B)=408,619+476,058*(B−8)` gate nodes for B≥8. This is their projection from the task brief, not a measurement made by this model. The representations differ; these numbers do not establish a hardware speedup.

MCX costing uses the clean ladder: k≥2 controls cost `2k−3` Toffolis and need k−2 clean ancillas. X and CX contribute zero Toffoli-equivalent gates. `peak_qubits` reserves the largest such ladder pool for the entire oracle; `native_peak_wires` excludes it. The emitter emits native MCX, not the decomposition. The MCX column below aggregates control counts ≥3; the JSON retains the complete histogram.

The `tradeoff.csv` columns are exactly the requested eight. `steps_executed` counts expanded forward/inverse **compiled block-step invocations**, including recomputation and the final oracle reversal, rather than input-dependent source rows. `checkpoints` is the maximum additional state-token count used by the regular strategy; zero denotes direct history. Budgets are quantum peak budgets and are distinct from the classical `(B,heap,stack,depth)` tuple. Collatz uses `(heap,stack,depth)=(0,32,32)`; the other measured fixtures have zero heap/stack/depth.

The following is the measured Collatz description/compilation scaling, with the tightest fixed quota beside unlimited space. B grows by more than eight orders of magnitude. Term count, compile time and RSS do not grow linearly with B. Counter widths and nested-definition levels grow logarithmically; the measurements are not a claim of strict constant time or memory.

| B | Unlimited DAG nodes | Tight DAG nodes | Unlimited ms | Tight ms | Unlimited RSS MiB | Tight RSS MiB |
|---|---|---|---|---|---|---|
| 9 | 11,968 | 11,968 | 218.879 | 168.732 | 23.648 | 23.648 |
| 28 | 12,116 | 12,116 | 176.470 | 159.813 | 23.758 | 23.746 |
| 100 | 12,281 | 37,865 | 207.685 | 224.603 | 24.012 | 23.969 |
| 2,048 | 13,160 | 13,615 | 163.435 | 292.635 | 24.973 | 25.027 |
| 1,000,000 | 14,318 | 14,895 | 196.587 | 280.590 | 28.641 | 28.477 |
| 1,000,000,000 | 15,806 | 32,178 | 192.954 | 346.004 | 29.840 | 29.566 |

## Complete measurement grid

Every gate/qubit entry in these tables is C; compile time and RSS are W. Tables are a snapshot of `measurements.json`. Integers are shown exactly; RSS is converted from KiB to MiB. The full control-count histograms and strategy choices are retained in JSON, and `tradeoff.csv` is provided for charting.

### inc8

| B | Peak budget | Qubits | X | CX | CCX | MCX | Toffoli eq. | Native gates | Compile ms | RSS MiB |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | unlimited | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.453 | 2.984 |
| 9 | 567 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 1.878 | 2.980 |
| 9 | 931 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.525 | 3.008 |
| 9 | 1,763 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.690 | 2.992 |
| 9 | 6,755 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.753 | 3.000 |
| 28 | unlimited | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 1.938 | 2.984 |
| 28 | 567 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.164 | 2.980 |
| 28 | 931 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.358 | 2.996 |
| 28 | 1,763 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.583 | 3.000 |
| 28 | 6,755 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.543 | 3.008 |
| 100 | unlimited | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.112 | 2.961 |
| 100 | 567 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.558 | 3.012 |
| 100 | 931 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 3.193 | 2.973 |
| 100 | 1,763 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.810 | 3.004 |
| 100 | 6,755 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.599 | 2.984 |
| 2,048 | unlimited | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 3.370 | 3.000 |
| 2,048 | 567 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.034 | 3.008 |
| 2,048 | 931 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.435 | 2.977 |
| 2,048 | 1,763 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.379 | 2.996 |
| 2,048 | 6,755 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.975 | 2.984 |
| 1,000,000 | unlimited | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 1.897 | 2.977 |
| 1,000,000 | 567 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 5.943 | 2.980 |
| 1,000,000 | 931 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.595 | 2.953 |
| 1,000,000 | 1,763 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.506 | 3.012 |
| 1,000,000 | 6,755 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.885 | 2.992 |
| 1,000,000,000 | unlimited | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 1.901 | 3.012 |
| 1,000,000,000 | 567 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.761 | 3.008 |
| 1,000,000,000 | 931 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.616 | 2.992 |
| 1,000,000,000 | 1,763 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 1.944 | 2.996 |
| 1,000,000,000 | 6,755 | 97 | 34 | 266 | 148 | 0 | 148 | 448 | 2.145 | 3.000 |

### collatz

| B | Peak budget | Qubits | X | CX | CCX | MCX | Toffoli eq. | Native gates | Compile ms | RSS MiB |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | unlimited | 3,633 | 3,982 | 49,542 | 17,428 | 0 | 17,428 | 70,952 | 218.879 | 23.648 |
| 9 | 7,241 | 3,633 | 3,982 | 49,542 | 17,428 | 0 | 17,428 | 70,952 | 168.732 | 23.648 |
| 9 | 10,545 | 3,633 | 3,982 | 49,542 | 17,428 | 0 | 17,428 | 70,952 | 212.990 | 23.621 |
| 9 | 18,097 | 3,633 | 3,982 | 49,542 | 17,428 | 0 | 17,428 | 70,952 | 190.135 | 23.645 |
| 9 | 63,409 | 3,633 | 3,982 | 49,542 | 17,428 | 0 | 17,428 | 70,952 | 159.741 | 23.598 |
| 28 | unlimited | 7,120 | 13,046 | 162,030 | 57,484 | 0 | 57,484 | 232,560 | 176.470 | 23.758 |
| 28 | 7,241 | 7,120 | 13,046 | 162,030 | 57,484 | 0 | 57,484 | 232,560 | 159.813 | 23.746 |
| 28 | 10,545 | 7,120 | 13,046 | 162,030 | 57,484 | 0 | 57,484 | 232,560 | 201.291 | 23.770 |
| 28 | 18,097 | 7,120 | 13,046 | 162,030 | 57,484 | 0 | 57,484 | 232,560 | 180.824 | 23.805 |
| 28 | 63,409 | 7,120 | 13,046 | 162,030 | 57,484 | 0 | 57,484 | 232,560 | 202.575 | 23.805 |
| 100 | unlimited | 20,346 | 48,690 | 607,178 | 215,224 | 0 | 215,224 | 871,092 | 207.685 | 24.012 |
| 100 | 7,241 | 6,797 | 154,078 | 2,304,306 | 914,736 | 0 | 914,736 | 3,373,120 | 224.603 | 23.969 |
| 100 | 10,545 | 6,797 | 154,078 | 2,304,306 | 914,736 | 0 | 914,736 | 3,373,120 | 231.035 | 24.012 |
| 100 | 18,097 | 11,562 | 145,494 | 1,814,496 | 643,352 | 0 | 643,352 | 2,603,342 | 181.343 | 24.012 |
| 100 | 63,409 | 20,346 | 48,690 | 607,178 | 215,224 | 0 | 215,224 | 871,092 | 188.185 | 23.992 |
| 2,048 | unlimited | 387,188 | 1,056,246 | 13,508,574 | 4,933,396 | 0 | 4,933,396 | 19,498,216 | 163.435 | 24.973 |
| 2,048 | 7,241 | 6,676 | 35,972,502 | 460,601,166 | 168,064,496 | 0 | 168,064,496 | 664,638,164 | 292.635 | 25.027 |
| 2,048 | 10,545 | 8,785 | 14,883,670 | 221,885,630 | 88,395,600 | 0 | 88,395,600 | 325,164,900 | 323.522 | 29.926 |
| 2,048 | 18,097 | 14,629 | 3,308,414 | 49,338,072 | 19,652,884 | 0 | 19,652,884 | 72,299,370 | 194.764 | 24.980 |
| 2,048 | 63,409 | 14,629 | 3,308,414 | 49,338,072 | 19,652,884 | 0 | 19,652,884 | 72,299,370 | 182.967 | 25.008 |
| 1,000,000 | unlimited | 196,002,316 | 627,999,422 | 7,095,991,558 | 2,713,997,580 | 0 | 2,713,997,580 | 10,437,988,560 | 196.587 | 28.641 |
| 1,000,000 | 7,241 | 6,824 | 1,946,085,963,958 | 22,140,509,189,038 | 8,410,379,714,432 | 0 | 8,410,379,714,432 | 32,496,974,867,428 | 280.590 | 28.477 |
| 1,000,000 | 10,545 | 9,753 | 310,511,311,254 | 4,328,678,734,686 | 1,744,502,886,928 | 0 | 1,744,502,886,928 | 6,383,692,932,868 | 403.540 | 31.504 |
| 1,000,000 | 18,097 | 15,397 | 137,841,431,574 | 1,920,992,811,990 | 774,275,882,632 | 0 | 774,275,882,632 | 2,833,110,126,196 | 352.168 | 31.414 |
| 1,000,000 | 63,409 | 38,617 | 61,240,248,726 | 853,478,820,750 | 344,000,635,744 | 0 | 344,000,635,744 | 1,258,719,705,220 | 316.621 | 31.418 |
| 1,000,000,000 | unlimited | 206,000,002,512 | 755,999,999,358 | 7,751,999,991,270 | 3,105,999,997,404 | 0 | 3,105,999,997,404 | 11,613,999,988,032 | 192.954 | 29.840 |
| 1,000,000,000 | 7,241 | 6,781 | 30,009,653,987,058,166 | 214,808,444,033,199,818 | 101,279,192,355,629,048 | 56,809,612,697,108,344 | 2,544,092,538,331,287,840 | 402,906,903,072,995,376 | 346.004 | 29.566 |
| 1,000,000,000 | 10,545 | 10,251 | 30,009,653,987,058,166 | 391,726,375,906,954,994 | 159,981,457,405,946,184 | 0 | 159,981,457,405,946,184 | 581,717,487,299,959,344 | 335.669 | 33.688 |
| 1,000,000,000 | 18,097 | 16,573 | 8,870,378,081,692,054 | 115,714,332,985,672,634 | 47,270,239,317,554,208 | 0 | 47,270,239,317,554,208 | 171,854,950,384,918,896 | 413.456 | 33.582 |
| 1,000,000,000 | 63,409 | 39,225 | 3,941,357,416,147,030 | 51,415,032,124,789,682 | 21,003,492,300,701,784 | 0 | 21,003,492,300,701,784 | 76,359,881,841,638,496 | 375.679 | 33.547 |

### gcd

| B | Peak budget | Qubits | X | CX | CCX | MCX | Toffoli eq. | Native gates | Compile ms | RSS MiB |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | unlimited | 810 | 2,108 | 11,436 | 5,420 | 0 | 5,420 | 18,964 | 45.575 | 9.750 |
| 9 | 3,575 | 810 | 2,108 | 11,436 | 5,420 | 0 | 5,420 | 18,964 | 42.969 | 9.742 |
| 9 | 5,311 | 810 | 2,108 | 11,436 | 5,420 | 0 | 5,420 | 18,964 | 54.947 | 9.754 |
| 9 | 9,279 | 810 | 2,108 | 11,436 | 5,420 | 0 | 5,420 | 18,964 | 48.556 | 9.742 |
| 9 | 33,087 | 810 | 2,108 | 11,436 | 5,420 | 0 | 5,420 | 18,964 | 50.023 | 9.645 |
| 28 | unlimited | 1,744 | 7,396 | 40,540 | 19,612 | 0 | 19,612 | 67,548 | 41.877 | 10.086 |
| 28 | 3,575 | 1,744 | 7,396 | 40,540 | 19,612 | 0 | 19,612 | 67,548 | 44.463 | 10.125 |
| 28 | 5,311 | 1,744 | 7,396 | 40,540 | 19,612 | 0 | 19,612 | 67,548 | 63.051 | 10.062 |
| 28 | 9,279 | 1,744 | 7,396 | 40,540 | 19,612 | 0 | 19,612 | 67,548 | 54.780 | 10.078 |
| 28 | 33,087 | 1,744 | 7,396 | 40,540 | 19,612 | 0 | 19,612 | 67,548 | 56.688 | 10.129 |
| 100 | unlimited | 5,178 | 27,356 | 153,204 | 74,500 | 0 | 74,500 | 255,060 | 66.334 | 10.277 |
| 100 | 3,575 | 1,193 | 135,852 | 384,704 | 188,348 | 0 | 188,348 | 708,904 | 63.051 | 10.062 |
| 100 | 5,311 | 5,178 | 27,356 | 153,204 | 74,500 | 0 | 74,500 | 255,060 | 49.787 | 10.082 |
| 100 | 9,279 | 5,178 | 27,356 | 153,204 | 74,500 | 0 | 74,500 | 255,060 | 43.537 | 10.285 |
| 100 | 33,087 | 5,178 | 27,356 | 153,204 | 74,500 | 0 | 74,500 | 255,060 | 59.613 | 10.145 |
| 2,048 | unlimited | 107,092 | 603,296 | 3,928,184 | 1,940,920 | 0 | 1,940,920 | 6,472,400 | 60.054 | 11.242 |
| 2,048 | 3,575 | 2,689 | 13,044,188 | 40,853,520 | 20,044,116 | 0 | 20,044,116 | 73,941,824 | 101.379 | 11.457 |
| 2,048 | 5,311 | 4,181 | 8,697,596 | 27,241,668 | 13,365,380 | 0 | 13,365,380 | 49,304,644 | 100.216 | 11.371 |
| 2,048 | 9,279 | 7,165 | 2,899,280 | 9,080,668 | 4,455,216 | 0 | 4,455,216 | 16,435,164 | 56.932 | 11.227 |
| 2,048 | 33,087 | 7,165 | 2,899,280 | 9,080,668 | 4,455,216 | 0 | 4,455,216 | 16,435,164 | 57.665 | 11.227 |
| 1,000,000 | unlimited | 60,000,748 | 387,999,844 | 2,342,665,724 | 1,206,666,204 | 0 | 1,206,666,204 | 3,937,331,772 | 62.711 | 12.629 |
| 1,000,000 | 3,575 | 3,280 | 270,728,324,788 | 895,475,238,008 | 445,823,892,860 | 0 | 445,823,892,860 | 1,612,027,455,656 | 124.798 | 12.938 |
| 1,000,000 | 5,311 | 4,692 | 180,301,545,228 | 596,369,112,204 | 296,912,844,020 | 0 | 296,912,844,020 | 1,073,583,501,452 | 110.614 | 14.148 |
| 1,000,000 | 9,279 | 7,571 | 120,201,356,284 | 397,578,719,108 | 197,942,465,156 | 0 | 197,942,465,156 | 715,722,540,548 | 129.561 | 13.988 |
| 1,000,000 | 33,087 | 25,044 | 53,402,475,628 | 176,633,781,920 | 87,940,924,196 | 0 | 87,940,924,196 | 317,977,181,744 | 159.837 | 14.016 |
| 1,000,000,000 | unlimited | 70,000,000,944 | 494,666,666,468 | 2,902,666,665,532 | 1,539,999,999,420 | 0 | 1,539,999,999,420 | 4,937,333,331,420 | 86.455 | 14.730 |
| 1,000,000,000 | 3,575 | 3,548 | 26,040,246,643,191,308 | 91,734,755,130,580,672 | 46,200,437,676,361,908 | 0 | 46,200,437,676,361,908 | 163,975,439,450,133,888 | 166.242 | 15.758 |
| 1,000,000,000 | 5,311 | 4,200 | 17,323,847,369,824,004 | 61,027,274,630,022,292 | 30,735,858,312,552,604 | 0 | 30,735,858,312,552,604 | 109,086,980,312,398,900 | 217.243 | 15.320 |
| 1,000,000,000 | 9,279 | 8,369 | 7,699,488,463,711,700 | 27,122,803,905,126,592 | 13,660,382,777,140,204 | 0 | 13,660,382,777,140,204 | 48,482,675,145,978,496 | 200.205 | 15.277 |
| 1,000,000,000 | 33,087 | 25,411 | 3,421,098,313,038,044 | 12,051,373,322,007,568 | 6,069,690,557,426,692 | 0 | 6,069,690,557,426,692 | 21,542,162,192,472,304 | 151.617 | 15.594 |

### popcount

| B | Peak budget | Qubits | X | CX | CCX | MCX | Toffoli eq. | Native gates | Compile ms | RSS MiB |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | unlimited | 970 | 1,686 | 12,454 | 6,484 | 0 | 6,484 | 20,624 | 51.268 | 7.234 |
| 9 | 3,271 | 970 | 1,686 | 12,454 | 6,484 | 0 | 6,484 | 20,624 | 35.511 | 7.227 |
| 9 | 5,007 | 970 | 1,686 | 12,454 | 6,484 | 0 | 6,484 | 20,624 | 31.395 | 7.273 |
| 9 | 8,975 | 970 | 1,686 | 12,454 | 6,484 | 0 | 6,484 | 20,624 | 27.249 | 7.230 |
| 9 | 32,783 | 970 | 1,686 | 12,454 | 6,484 | 0 | 6,484 | 20,624 | 61.517 | 7.254 |
| 28 | unlimited | 2,056 | 5,858 | 42,850 | 22,640 | 0 | 22,640 | 71,348 | 36.043 | 7.242 |
| 28 | 3,271 | 2,056 | 5,858 | 42,850 | 22,640 | 0 | 22,640 | 71,348 | 67.202 | 7.492 |
| 28 | 5,007 | 2,056 | 5,858 | 42,850 | 22,640 | 0 | 22,640 | 71,348 | 29.707 | 7.539 |
| 28 | 8,975 | 2,056 | 5,858 | 42,850 | 22,640 | 0 | 22,640 | 71,348 | 36.270 | 7.527 |
| 28 | 32,783 | 2,056 | 5,858 | 42,850 | 22,640 | 0 | 22,640 | 71,348 | 38.113 | 7.535 |
| 100 | unlimited | 6,066 | 21,718 | 161,910 | 85,780 | 0 | 85,780 | 269,408 | 39.294 | 7.395 |
| 100 | 3,271 | 989 | 92,530 | 288,718 | 146,392 | 0 | 146,392 | 527,640 | 53.712 | 7.637 |
| 100 | 5,007 | 989 | 92,530 | 288,718 | 146,392 | 0 | 146,392 | 527,640 | 39.381 | 7.637 |
| 100 | 8,975 | 6,066 | 21,718 | 161,910 | 85,780 | 0 | 85,780 | 269,408 | 37.974 | 7.637 |
| 100 | 32,783 | 6,066 | 21,718 | 161,910 | 85,780 | 0 | 85,780 | 269,408 | 39.132 | 7.414 |
| 2,048 | unlimited | 123,564 | 483,234 | 4,045,554 | 2,141,480 | 0 | 2,141,480 | 6,670,268 | 52.099 | 8.625 |
| 2,048 | 3,271 | 2,897 | 8,992,274 | 31,549,498 | 15,955,784 | 0 | 15,955,784 | 56,497,556 | 96.010 | 8.684 |
| 2,048 | 5,007 | 4,901 | 5,995,282 | 21,035,426 | 10,638,264 | 0 | 10,638,264 | 37,668,972 | 75.505 | 8.512 |
| 2,048 | 8,975 | 8,909 | 1,998,546 | 7,012,404 | 3,546,380 | 0 | 3,546,380 | 12,557,330 | 58.130 | 8.570 |
| 2,048 | 32,783 | 8,909 | 1,998,546 | 7,012,404 | 3,546,380 | 0 | 3,546,380 | 12,557,330 | 46.111 | 8.504 |
| 1,000,000 | unlimited | 68,000,836 | 319,999,850 | 2,363,998,490 | 1,281,999,136 | 0 | 1,281,999,136 | 3,965,997,476 | 43.871 | 9.766 |
| 1,000,000 | 3,271 | 2,541 | 288,553,531,746 | 1,066,179,899,082 | 545,936,219,992 | 0 | 545,936,219,992 | 1,900,669,650,820 | 105.586 | 10.062 |
| 1,000,000 | 5,007 | 3,465 | 191,968,045,026 | 709,220,598,162 | 363,171,834,808 | 0 | 363,171,834,808 | 1,264,360,477,996 | 113.729 | 10.051 |
| 1,000,000 | 8,975 | 5,365 | 127,845,130,818 | 472,292,279,202 | 241,852,901,464 | 0 | 241,852,901,464 | 841,990,311,484 | 96.900 | 10.027 |
| 1,000,000 | 32,783 | 32,553 | 37,864,867,074 | 139,875,290,970 | 71,629,127,224 | 0 | 71,629,127,224 | 249,369,285,268 | 93.435 | 10.012 |
| 1,000,000,000 | unlimited | 78,000,001,032 | 415,999,999,786 | 2,875,999,998,202 | 1,585,999,998,960 | 0 | 1,585,999,998,960 | 4,877,999,996,948 | 62.765 | 11.094 |
| 1,000,000,000 | 3,271 | 3,069 | 28,559,266,139,024,146 | 111,966,693,126,435,542 | 57,841,548,066,234,408 | 0 | 57,841,548,066,234,408 | 198,367,507,331,694,096 | 107.336 | 11.105 |
| 1,000,000,000 | 5,007 | 4,373 | 12,614,570,141,279,794 | 49,455,826,417,564,358 | 25,550,202,433,902,360 | 0 | 25,550,202,433,902,360 | 87,620,598,992,746,512 | 135.185 | 11.547 |
| 1,000,000,000 | 8,975 | 6,219 | 8,409,118,707,562,706 | 32,964,974,127,034,954 | 17,031,126,045,362,216 | 0 | 17,031,126,045,362,216 | 58,405,218,879,959,876 | 114.095 | 11.465 |
| 1,000,000,000 | 32,783 | 32,737 | 2,490,937,979,430,610 | 9,764,729,136,460,514 | 5,044,937,623,488,552 | 0 | 5,044,937,623,488,552 | 17,300,604,739,379,676 | 106.256 | 11.461 |

### diamond

| B | Peak budget | Qubits | X | CX | CCX | MCX | Toffoli eq. | Native gates | Compile ms | RSS MiB |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | unlimited | 948 | 1,778 | 13,050 | 6,260 | 0 | 6,260 | 21,088 | 51.253 | 10.547 |
| 9 | 3,416 | 948 | 1,778 | 13,050 | 6,260 | 0 | 6,260 | 21,088 | 55.111 | 10.570 |
| 9 | 5,152 | 948 | 1,778 | 13,050 | 6,260 | 0 | 6,260 | 21,088 | 62.624 | 10.578 |
| 9 | 9,120 | 948 | 1,778 | 13,050 | 6,260 | 0 | 6,260 | 21,088 | 58.832 | 10.578 |
| 9 | 32,928 | 948 | 1,778 | 13,050 | 6,260 | 0 | 6,260 | 21,088 | 57.175 | 10.582 |
| 28 | unlimited | 2,034 | 6,214 | 45,198 | 22,032 | 0 | 22,032 | 73,444 | 53.456 | 10.863 |
| 28 | 3,416 | 2,034 | 6,214 | 45,198 | 22,032 | 0 | 22,032 | 73,444 | 56.388 | 11.012 |
| 28 | 5,152 | 2,034 | 6,214 | 45,198 | 22,032 | 0 | 22,032 | 73,444 | 69.619 | 11.012 |
| 28 | 9,120 | 2,034 | 6,214 | 45,198 | 22,032 | 0 | 22,032 | 73,444 | 65.066 | 11.000 |
| 28 | 32,928 | 2,034 | 6,214 | 45,198 | 22,032 | 0 | 22,032 | 73,444 | 60.882 | 10.957 |
| 100 | unlimited | 6,044 | 22,798 | 168,902 | 82,888 | 0 | 82,888 | 274,588 | 58.334 | 11.188 |
| 100 | 3,416 | 1,134 | 122,486 | 351,700 | 164,496 | 0 | 164,496 | 638,682 | 76.599 | 10.895 |
| 100 | 5,152 | 1,134 | 122,486 | 351,700 | 164,496 | 0 | 164,496 | 638,682 | 60.666 | 11.184 |
| 100 | 9,120 | 6,044 | 22,798 | 168,902 | 82,888 | 0 | 82,888 | 274,588 | 85.194 | 11.207 |
| 100 | 32,928 | 6,044 | 22,798 | 168,902 | 82,888 | 0 | 82,888 | 274,588 | 77.566 | 10.977 |
| 2,048 | unlimited | 123,542 | 503,806 | 4,177,422 | 2,076,360 | 0 | 2,076,360 | 6,757,588 | 58.192 | 12.305 |
| 2,048 | 3,416 | 3,042 | 11,731,702 | 37,256,814 | 17,574,544 | 0 | 17,574,544 | 66,563,060 | 135.156 | 12.445 |
| 2,048 | 5,152 | 5,046 | 7,821,190 | 24,838,342 | 11,716,448 | 0 | 11,716,448 | 44,375,980 | 127.641 | 12.422 |
| 2,048 | 9,120 | 9,054 | 2,607,090 | 8,279,564 | 3,905,532 | 0 | 3,905,532 | 14,792,186 | 71.700 | 12.324 |
| 2,048 | 32,928 | 9,054 | 2,607,090 | 8,279,564 | 3,905,532 | 0 | 3,905,532 | 14,792,186 | 77.709 | 11.918 |
| 1,000,000 | unlimited | 68,000,814 | 329,999,998 | 2,427,999,502 | 1,249,999,688 | 0 | 1,249,999,688 | 4,007,999,188 | 85.563 | 14.699 |
| 1,000,000 | 3,416 | 2,686 | 365,769,051,574 | 1,226,447,101,878 | 591,201,468,808 | 0 | 591,201,468,808 | 2,183,417,622,260 | 172.995 | 14.594 |
| 1,000,000 | 5,152 | 3,610 | 243,382,037,134 | 816,070,250,398 | 393,389,893,760 | 0 | 393,389,893,760 | 1,452,842,181,292 | 157.768 | 14.809 |
| 1,000,000 | 9,120 | 5,510 | 162,100,033,870 | 543,526,572,414 | 262,011,801,424 | 0 | 262,011,801,424 | 967,638,407,708 | 159.960 | 14.773 |
| 1,000,000 | 32,928 | 32,698 | 48,014,131,414 | 160,992,545,014 | 77,608,539,416 | 0 | 77,608,539,416 | 286,615,215,844 | 165.853 | 14.789 |
| 1,000,000,000 | unlimited | 78,000,001,010 | 425,999,999,998 | 2,939,999,999,502 | 1,553,999,999,688 | 0 | 1,553,999,999,688 | 4,919,999,999,188 | 109.733 | 16.355 |
| 1,000,000,000 | 3,416 | 3,214 | 35,269,799,911,767,526 | 125,930,049,272,721,418 | 61,795,581,709,627,616 | 0 | 61,795,581,709,627,616 | 222,995,430,894,116,560 | 177.039 | 16.406 |
| 1,000,000,000 | 5,152 | 4,518 | 15,575,140,335,061,318 | 55,606,059,162,007,882 | 27,288,606,592,304,936 | 0 | 27,288,606,592,304,936 | 98,469,806,089,374,136 | 211.870 | 16.992 |
| 1,000,000,000 | 9,120 | 6,364 | 10,383,653,168,772,286 | 37,070,611,953,495,210 | 18,192,488,114,046,232 | 0 | 18,192,488,114,046,232 | 65,646,753,236,313,728 | 161.135 | 16.805 |
| 1,000,000,000 | 32,928 | 32,882 | 3,076,179,971,753,542 | 10,982,394,939,044,938 | 5,389,700,159,671,664 | 0 | 5,389,700,159,671,664 | 19,448,275,070,470,144 | 189.304 | 16.855 |

### irreducible

| B | Peak budget | Qubits | X | CX | CCX | MCX | Toffoli eq. | Native gates | Compile ms | RSS MiB |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | unlimited | 1,059 | 2,888 | 17,000 | 8,896 | 0 | 8,896 | 28,784 | 43.816 | 8.785 |
| 9 | 3,343 | 1,059 | 2,888 | 17,000 | 8,896 | 0 | 8,896 | 28,784 | 47.237 | 8.777 |
| 9 | 4,855 | 1,059 | 2,888 | 17,000 | 8,896 | 0 | 8,896 | 28,784 | 39.441 | 8.758 |
| 9 | 8,311 | 1,059 | 2,888 | 17,000 | 8,896 | 0 | 8,896 | 28,784 | 40.011 | 8.785 |
| 9 | 29,047 | 1,059 | 2,888 | 17,000 | 8,896 | 0 | 8,896 | 28,784 | 46.735 | 8.734 |
| 28 | unlimited | 2,012 | 10,180 | 59,812 | 31,852 | 0 | 31,852 | 101,844 | 52.209 | 9.141 |
| 28 | 3,343 | 2,012 | 10,180 | 59,812 | 31,852 | 0 | 31,852 | 101,844 | 43.230 | 9.180 |
| 28 | 4,855 | 2,012 | 10,180 | 59,812 | 31,852 | 0 | 31,852 | 101,844 | 49.687 | 9.121 |
| 28 | 8,311 | 2,012 | 10,180 | 59,812 | 31,852 | 0 | 31,852 | 101,844 | 59.896 | 9.152 |
| 28 | 29,047 | 2,012 | 10,180 | 59,812 | 31,852 | 0 | 31,852 | 101,844 | 50.635 | 9.156 |
| 100 | unlimited | 5,456 | 37,812 | 227,508 | 121,596 | 0 | 121,596 | 386,916 | 46.408 | 9.215 |
| 100 | 3,343 | 1,131 | 154,612 | 401,282 | 184,512 | 0 | 184,512 | 740,406 | 45.744 | 9.270 |
| 100 | 4,855 | 1,131 | 154,612 | 401,282 | 184,512 | 0 | 184,512 | 740,406 | 56.225 | 9.016 |
| 100 | 8,311 | 5,456 | 37,812 | 227,508 | 121,596 | 0 | 121,596 | 386,916 | 70.472 | 9.371 |
| 100 | 29,047 | 5,456 | 37,812 | 227,508 | 121,596 | 0 | 121,596 | 386,916 | 57.935 | 9.359 |
| 2,048 | unlimited | 107,424 | 839,468 | 5,818,316 | 3,103,548 | 0 | 3,103,548 | 9,761,332 | 74.545 | 10.520 |
| 2,048 | 3,343 | 3,069 | 15,035,156 | 44,876,436 | 20,855,244 | 0 | 20,855,244 | 80,766,836 | 107.226 | 10.621 |
| 2,048 | 4,855 | 3,069 | 15,035,156 | 44,876,436 | 20,855,244 | 0 | 20,855,244 | 80,766,836 | 125.820 | 10.625 |
| 2,048 | 8,311 | 5,081 | 10,024,340 | 29,921,516 | 13,905,148 | 0 | 13,905,148 | 53,851,004 | 118.990 | 10.570 |
| 2,048 | 29,047 | 9,105 | 3,341,684 | 9,974,810 | 4,635,488 | 0 | 4,635,488 | 17,951,982 | 71.128 | 10.348 |
| 1,000,000 | unlimited | 60,001,148 | 549,999,676 | 3,445,997,468 | 1,887,998,508 | 0 | 1,887,998,508 | 5,883,995,652 | 62.616 | 11.980 |
| 1,000,000 | 3,343 | 2,701 | 482,273,634,940 | 1,545,041,694,940 | 736,524,208,540 | 0 | 736,524,208,540 | 2,763,839,538,420 | 146.618 | 12.277 |
| 1,000,000 | 4,855 | 3,633 | 320,857,927,596 | 1,027,816,600,828 | 489,980,044,188 | 0 | 489,980,044,188 | 1,838,654,572,612 | 106.860 | 12.246 |
| 1,000,000 | 8,311 | 5,541 | 213,686,201,692 | 684,474,879,868 | 326,308,368,316 | 0 | 326,308,368,316 | 1,224,469,449,876 | 99.640 | 12.230 |
| 1,000,000 | 29,047 | 17,173 | 94,947,366,028 | 304,121,999,788 | 144,985,439,212 | 0 | 144,985,439,212 | 544,054,805,028 | 103.198 | 12.199 |
| 1,000,000,000 | unlimited | 70,000,001,432 | 709,999,999,548 | 4,245,999,996,892 | 2,367,999,998,156 | 0 | 2,367,999,998,156 | 7,323,999,994,596 | 74.899 | 14.621 |
| 1,000,000,000 | 3,343 | 3,229 | 47,719,276,767,089,684 | 164,994,123,721,903,520 | 80,164,763,731,524,844 | 0 | 80,164,763,731,524,844 | 292,878,164,220,518,048 | 163.803 | 14.555 |
| 1,000,000,000 | 4,855 | 4,549 | 21,076,547,292,402,092 | 72,876,688,489,621,568 | 35,409,151,338,875,932 | 0 | 35,409,151,338,875,932 | 129,362,387,120,899,592 | 163.606 | 14.973 |
| 1,000,000,000 | 8,311 | 6,403 | 14,050,678,938,979,604 | 48,578,999,771,359,104 | 23,604,075,404,553,948 | 0 | 23,604,075,404,553,948 | 86,233,754,114,892,656 | 167.880 | 14.734 |
| 1,000,000,000 | 29,047 | 17,739 | 6,243,129,790,876,508 | 21,585,167,698,182,912 | 10,488,064,526,882,220 | 0 | 10,488,064,526,882,220 | 38,316,362,015,941,640 | 166.554 | 14.664 |

### faultif

| B | Peak budget | Qubits | X | CX | CCX | MCX | Toffoli eq. | Native gates | Compile ms | RSS MiB |
|---|---|---|---|---|---|---|---|---|---|---|
| 9 | unlimited | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.700 | 3.301 |
| 9 | 620 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.616 | 3.320 |
| 9 | 1,012 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 9.892 | 3.301 |
| 9 | 1,908 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.026 | 3.312 |
| 9 | 7,284 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 7.050 | 3.332 |
| 28 | unlimited | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.183 | 3.273 |
| 28 | 620 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.416 | 3.320 |
| 28 | 1,012 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.443 | 3.312 |
| 28 | 1,908 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.717 | 3.312 |
| 28 | 7,284 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.610 | 3.281 |
| 100 | unlimited | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.225 | 3.332 |
| 100 | 620 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.723 | 3.336 |
| 100 | 1,012 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.516 | 3.281 |
| 100 | 1,908 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.897 | 3.305 |
| 100 | 7,284 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.133 | 3.289 |
| 2,048 | unlimited | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.723 | 3.309 |
| 2,048 | 620 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.616 | 3.293 |
| 2,048 | 1,012 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.015 | 3.316 |
| 2,048 | 1,908 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.548 | 3.297 |
| 2,048 | 7,284 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.843 | 3.305 |
| 1,000,000 | unlimited | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.808 | 3.324 |
| 1,000,000 | 620 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 3.772 | 3.293 |
| 1,000,000 | 1,012 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.432 | 3.324 |
| 1,000,000 | 1,908 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.629 | 3.277 |
| 1,000,000 | 7,284 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.743 | 3.320 |
| 1,000,000,000 | unlimited | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.099 | 3.293 |
| 1,000,000,000 | 620 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.174 | 3.305 |
| 1,000,000,000 | 1,012 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 3.851 | 3.320 |
| 1,000,000,000 | 1,908 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 5.238 | 3.328 |
| 1,000,000,000 | 7,284 | 127 | 190 | 566 | 278 | 0 | 278 | 1,034 | 4.921 | 3.281 |

## Reproduction and remaining work

From `model/`:

```
cargo test --offline
cargo run --release --offline
cargo run --release --offline -- --verify-boundaries
python3 report.py
```

The crate is Rust edition 2024, std only, with no dependencies. The optional report formatter uses only Python's standard library. `--one FIXTURE B [PEAK|unlimited]` emits one JSON record. `--emit` streams the flat line format; `--hierarchy` writes a shared `.pcirc` description. Flat emission at large B has expanded runtime/output size and is intentionally not part of the large-B benchmark. Example descriptions and a small flat circuit are under `results/`.

Limits to address next: lift the context/period caps (4096 inline contexts, 65536 reachability phases); strengthen affine time-indexed counter and per-phase rank/layout analysis; optimize variable-elimination order and wide odd inverses; relate the regular large planner to DP/lower bounds; provide a derivation checker for all data-path optimizations independently of exhaustive fixture testing; then add classical-address memory and sum_db. The exact solver for Eval-only small DAGs is also left to the stretch track. No global optimality, arbitrary-width exhaustive coverage, memory-oracle support, or Linux-kernel-scale compilation is claimed.
