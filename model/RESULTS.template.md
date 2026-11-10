# Pebble executable model — results

**Status.** M0–M6 have executable implementations for the supported memory-free subset. {{TESTS}} unit tests pass. The final boundary harness records {{BOUNDARY_RUNS}} passing circuit/budget/control instances, covering {{BOUNDARY_CASES}} interface basis assignments algebraically; no final failing instance was found. Collatz's optimized frame has **four bits: three predecessor-rank bits and one data-residue bit**. The exact chain solver and nested DP have largest observed additive gap **{{GAP}}** on {{CHAIN_INSTANCES}} recorded instances.

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
| M6 | Seven fixtures × six B values × unlimited/four fixed peak budgets; actual selected circuit costs; fresh-process compile time and RSS | {{MEASUREMENTS}} measured compilation records. Quotas are fixed across B for each fixture. Costs are exact under the stated gate/decomposition model. Correctness simulation has the separately documented finite domains. |

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

{{RESIDUE_TABLE}}

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

The recorded comparison grid has 342 uniform instances (T=1…6, m=1…2, r=0…2, S=m…10, a=2, k=1) and 32 nonuniform instances at T=5. The largest observed gap is {{GAP}} and the number of nested reachability misses is {{MISSES}}. Exact per-instance costs and explored-state counts are in `chain.csv`.

For large T, a regular strategy stores leaf length ℓ and level count d, pads to `ℓ*2^d≥T`, and has clean-compute peak `(2+d)m+ℓr`, `2ℓ*3^d` step moves and `3^d` copies. A separate checker recomputes these quantities and the legal leaf/split invariants. The circuit reuses definitions and maps a finite-prefix/periodic step family through each segment. For a fixed program the number of schedule definitions is O(log T). The actual nonuniform gate costs are then recomputed from the emitted term DAG. The selection score uses a maximum step price; it need not choose the best nonuniform schedule.

{{PLANNING}}

`best` compares full-old-state, Boolean-inverse residue, and compact in-place-inverse residue candidates, using structural Toffoli count, native gate count, and peak as the ordering. Each candidate uses direct history when it fits and otherwise a checked regular schedule. Failure to find a strategy in these families does not prove global infeasibility.

## Measurement conventions

- **C: computed by structural recursion.** Native gate histogram, expanded native gate count, native peak live allocation and MCX-decomposed qubits/Toffoli count. No expanded gate list is built. Histogram key k means k positive controls: 0=X, 1=CX, 2=CCX, ≥3=MCX.
- **W: measured.** `compile_us` covers parsing, all candidate construction, scheduling and cost selection in a fresh release-mode subprocess. `peak_rss_kib` is that process's Linux `VmHWM`, including runtime/image overhead, not a heap-only delta. Parent process startup is excluded from compile time.
- **V: verified by simulation.** The separate verification CSVs identify finite circuit/budget/control instances. The cost grid's `simulation` field is false.
- **P: supplied projection.** The parent project's legacy-generator analysis projects `G(B)=408,619+476,058*(B−8)` gate nodes for B≥8. This is their projection from the task brief, not a measurement made by this model. The representations differ; these numbers do not establish a hardware speedup.

MCX costing uses the clean ladder: k≥2 controls cost `2k−3` Toffolis and need k−2 clean ancillas. X and CX contribute zero Toffoli-equivalent gates. `peak_qubits` reserves the largest such ladder pool for the entire oracle; `native_peak_wires` excludes it. The emitter emits native MCX, not the decomposition. The MCX column below aggregates control counts ≥3; the JSON retains the complete histogram.

The `tradeoff.csv` columns are exactly the requested eight. `steps_executed` counts expanded forward/inverse **compiled block-step invocations**, including recomputation and the final oracle reversal, rather than input-dependent source rows. `checkpoints` is the maximum additional state-token count used by the regular strategy; zero denotes direct history. Budgets are quantum peak budgets and are distinct from the classical `(B,heap,stack,depth)` tuple. Collatz uses `(heap,stack,depth)=(0,32,32)`; the other measured fixtures have zero heap/stack/depth.

{{SCALING}}

## Complete measurement grid

Every gate/qubit entry in these tables is C; compile time and RSS are W. Tables are a snapshot of `measurements.json`. Integers are shown exactly; RSS is converted from KiB to MiB. The full control-count histograms and strategy choices are retained in JSON, and `tradeoff.csv` is provided for charting.

{{MEASUREMENT_TABLES}}

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
