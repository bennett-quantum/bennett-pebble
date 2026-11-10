# Handoff — Pebble, an optimising pebbling circuit compiler for Bennett

Session of 2026-11-10. Owner of the session: Claude (Fable 5.2), working for
the maintainer, with three delegated tracks (Codex gpt-6.1-sol). This file is
the single entry point; everything it cites is in this repository.

## 1. Why this exists

The Bennett workspace's circuit generator (`bennett-circuits`) is a literal
bounded specialiser. It runs out of memory on a basic Collatz oracle. The
workspace plan commits to an "optimising specialiser and scheduler" (bead
`bennett-p2i`, `bennett/docs/plan/2026-10-29-path-to-north-star.md`) but has no
design for it; the 2026-11-09 exporter redesign in `bennett-circuits`
explicitly defers pebbling. The brief for this session was to *imagine* that
compiler: a design, with analytic and formal justification and a functioning
model. Collatz is the baseline; the north star is compiling the Linux kernel,
so every choice is judged by whether it survives 10⁹+ step budgets.

## 2. What was produced

| Track | Artefact | Who | State |
|---|---|---|---|
| Design | `docs/DESIGN.md` | Claude | complete; §7 holds results |
| Formal core | `docs/CORE.md` (revision 2) | Claude | complete; corrections marked **[R2]** |
| Analytic proofs | `docs/THEORY.md`, `theory/*.py` | delegate (sol, xhigh) | complete |
| k-ary frontier | `theory/kary_frontier.py`, `.json` | Claude | complete |
| Mechanisation | `formal/` (Lean 4.35, no Mathlib) | delegate (sol, high) | complete; rebuilt clean by Claude |
| Executable model | `model/` (Rust, std only) | delegate (sol, high) | functionally complete; **cancelled at wind-up before its final report** |

### The design in six sentences

1. The target is the oracle function F_B from ISA §5.2/§14.1, not the step
   machine; the budget is a comparison on a row counter.
2. Classical data is staged away by partial evaluation (only for classically
   addressed state).
3. Garbage is information: each step leaves a *residue* just large enough to
   invert it, found by a small calculus of sound rules (Eval, Copy, InPlace,
   Relabel, Guard).
4. History is a one-dimensional pebble game with two currencies, residues and
   full-state checkpoints, played under a peak-qubit cap.
5. The optimiser is untrusted: it must output a sequence of sound moves that
   an independent checker replays.
6. Nothing is materialised: the circuit is a shared DAG of definitions (gate,
   seq, call, adj, ctrl, rep, with), priced by recursion and emitted by
   streaming.

## 3. Results

**Lean.** 65 theorems, no `sorry`/`admit`, no added axioms (`formal/axioms.txt`).
Headline: `oracle_contract`, `dirty_oracle_contract`, `oracle_controlled`,
`calculus_sound`, `DAG.strategy_sound`, `Chain.legal_play_oracle`,
`Chain.accepts_iff_legal`. Two counterexamples correct CORE revision 1:
`physical_relabel_not_zero_gates`, `empty_play_legal_without_goal`.

**Theory.** Oracle contract on the full domain including entangled inputs.
Chain game: exact unrestricted search (ground truth, exponential); a nested
class with an exact interval recurrence that matched the unrestricted optimum
on 650 instances (theory track) and 374 more (model track); a loose lower
bound; the balanced κ-ary family with closed-form cost and peak. Ghost pebbles
(measurement-based uncomputation): correction rule proved, outside ISA 0.9.

**Model** (`model/RESULTS.md` is the full report).

- Residue per step, bits: Collatz 206 → 4, gcd 70 → 3, popcount 78 → 4,
  irreducible two-entry loop 70 → 4.
- Collatz, B = 2048: 4.9M Toffoli-equivalents at 387k qubits; 19.7M at 14.6k;
  88M at 8.8k; 168M at 6.7k. The legacy exporter was projected at ~972M gate
  nodes for this budget and does not finish.
- Compile time 0.2–0.35 s and 24–30 MiB from B = 9 to B = 10⁹.
- Verification: 2,198 circuit/budget/control instances agree with the
  reference interpreter on every 8-bit input and, symbolically, every initial
  target/fault value.

**Kernel-scale arithmetic** (`theory/kary_frontier.py`). For 10⁹ steps, 1,000
live bits, 1 residue bit per step, the replay factor over an irreversible run
is 551× at a 30k-qubit cap, 27× at 100k, 7.9× at 300k, 4.0× at 3M; the floor is
2×. At 100 residue bits per step, 100k qubits costs 101×. Residue width is the
main lever. These schedules are legal but not proved optimal (within 1.53× of
the exact nested optimum on 85 small instances).

## 4. What is checked, and by whom

| Claim | Evidence | Independently re-checked by Claude |
|---|---|---|
| Lean theorems hold | `lake build` | yes: clean rebuild |
| Theory corrections to CORE | `docs/THEORY.md` | read and folded into CORE R2; proofs not re-derived line by line |
| k-ary frontier | script output | yes: written and run by Claude |
| Model tests pass | `cargo test --offline` | yes: 39 pass |
| Model emits gates matching its cost count | `--emit collatz 28` | yes: 232,560 gates both ways |
| Model B = 10⁹ description | `--hierarchy collatz 1000000000 10000` | yes: 43,958 definitions, 0.5 s |
| Model measurement grid, boundary verification | `model/results/*` | **no**: files are the delegate's last run (10:11, after its last source edit at 10:08); not re-run |
| Model source | `model/src/*.rs`, ~6,200 lines | **no**: not line-reviewed |

`model/RESULTS.md` was rendered by Claude with the delegate's own `report.py`
from `RESULTS.template.md` and `results/`. The delegate never delivered a
closing summary, so anything it knew and had not yet written down is lost.

One retraction: Claude earlier suspected an integer overflow because a B = 10⁹
row shows fewer native gates than Toffoli-equivalents. That is explained by
the costing convention (a k-control MCX is one native gate but 2k−3
Toffolis). Overflow was not separately ruled out.

## 5. Known gaps and errors

1. **Model scheduler is binary only.** Large budgets use leaf ℓ and d binary
   levels. The design calls for wide fan-out. At B = 10⁹ and a 63,409-qubit
   cap the model replays each step ~3,900 times where a 60-ary 3-level
   schedule should need ~8 (formula estimate, unmeasured). This is the largest
   and cheapest win available.
2. **Model corrections not yet folded into CORE.** `model/RESULTS.md`
   "Corrections and interpretations of CORE" lists seven. Item 1 (horizon
   c ≥ B) is already in CORE R2. Items 2–6 are not: bit views
   (`Const | Wire`) are needed to state Lemma 2.4 and relabelling; in-place
   `x += x << k` needs k > 0; "memoryless" is narrower in ISA §7.2 than CORE
   uses it; rank and counter analysis are conservative; Theorem 7.2 needs
   injective maps and a fresh control.
3. **Principle 5 is not realised in the model.** Chain strategies are replayed
   by a checker, but data-path rewrites are trusted on the strength of
   exhaustive fixture tests. There is no derivation checker.
4. **No lifted memory.** `sum_db` and anything with a superposed address is
   rejected. The design's answer (§6 of DESIGN) is unproven in code.
5. **Per-step cost is unoptimised.** One Collatz step is ~19,400 native gates
   in the compact data path. No adder/multiplier selection was done.
6. **Idle steps cost full price.** At B = 10⁹ every 8-bit Collatz input except
   0 has halted by row 2,296 and the circuit idles for the rest. Truncating
   needs a proved halting bound; none is derived.
7. **Fixture header says ISA 0.8**; the parser does not authenticate envelopes.
8. **Open mathematics.** Is the nested class globally optimal? The lower bound
   is loose. Both in `docs/THEORY.md` Part C.
9. **Nobody has measured live-state width m or residue width r on a real
   workload.** Every kernel-scale number is conditional on them.

## 6. Ideas raised in discussion, not yet in the design

- **Budget search by amplitude amplification on the fault bit** (maintainer's
  suggestion). Sound as Dürr–Høyer maximum-finding on halt time, because
  budget faults are monotone in B and a miss is flagged by the fault bit.
  Obstacles: non-halting inputs pin the fault bit; there is no sound stopping
  rule without an a-priori budget; it competes with N classical runs.
- **Staged oracle for variable-time amplification.** Expose the oracle at
  budgets B₁ < B₂ < … with a done flag at each stage, continuing from the
  previous stage's state. The pebbling checkpoints are exactly those
  continuation points. A search caller then pays for root-mean-square halt
  time instead of the maximum (8-bit Collatz: 1,072 vs 2,296 rows). Worth a
  DESIGN section and probably an ISA note.
- **Measure-and-rerun** for callers that only want a classical answer; needs
  measurement, which ISA 0.9 does not admit.

## 7. Merging into the Bennett workspace

This repository is the proposed home: `bennett-quantum/bennett-pebble`. A
pointer note is in `bennett/docs/design/2026-11-10-pebble-optimising-compiler.md`
(committed locally in `bennett`, left for the orchestrator to push, per that
repository's git policy). It is not in `bennett/manifest.toml`, so no workspace
gate or script picks it up yet.

Suggested order, smallest commitment first:

1. **Adopt the design.** Council-review `docs/DESIGN.md` + `docs/CORE.md` as
   the design for `bennett-p2i`. `docs/THEORY.md` follows the precedent of
   `bennett-circuits/docs/design/2026-10-30-m2-open-proofs.md`.
2. **File the ISA feedback** against `bennett-isa-spec`: §17 item 18 must be
   wide enough to carry in-place erasures (they are sound but are not a §6
   `reverse`); measurement-based cleanup is a plan goal that 0.9 forbids; a
   staged-budget oracle interface.
3. **Use the model as a differential oracle** in `bennett-conformance`: its
   reference interpreter and exhaustive harness can check the real exporter on
   small fixtures without being production code.
4. **Rewrite, do not copy, into production repos** when the bead is worked:
   compiler and residue rules → `bennett-circuits`; chain scheduler →
   `bennett-sched`; gadgets → `bennett-arith`; cost recursion →
   `bennett-estimate`; hierarchical description consumer → `bennett-vm`. The
   roles of `sched`, `arith`, `estimate` and `vm` are inferred from their names
   and the plan; this session did not open them.
5. **Lean** has no home in a Rust-only workspace. Keep it here as evidence
   unless the workspace decides to carry a Lean toolchain.
6. Add to `manifest.toml` only when the repository meets the workspace's
   quality floor (it has no `gate.toml`, worklog, or beads).

## 8. Next work, in priority order

1. Wide fan-out scheduler in the model; re-measure the B = 10⁶ and 10⁹ rows.
2. Re-run the full measurement and boundary-verification grid; line-review
   `compiler.rs` and `optimized.rs`.
3. Fold model corrections 2–6 into CORE (revision 3).
4. Derivation checker for data-path rewrites.
5. Classically addressed memory, then `sum_db`.
6. Measure m and r on the SQLite spike workload
   (`bennett-dialect-spec/docs/spikes/sqlite/REPORT.md`).
7. Staged-oracle section in DESIGN.

## 9. Environment and housekeeping

- **Lean:** elan installed in `~/.elan` with `--no-modify-path`; use
  `~/.elan/bin/lake`. Toolchain 4.35.0.
- **Rust:** cargo 1.99.1, edition 2024, no dependencies, builds offline.
- **ISA spec:** all `§n` references are to `bennett-isa-spec` at the commit in
  `ref/isa-spec/SNAPSHOT_REV`. The copy is not committed; README has the
  restore command.
- **Workspace state left untouched:** `bennett-isa-spec` local `main` is 34
  commits behind with a modified `.beads/issues.jsonl` (not stashed, not
  pulled). `bennett-dialect-spec`, `bennett-driver` and `bennett-runtimes` had
  diverged from their remotes and were left alone. The untracked council files
  in `bennett` are not from this session.
- **Delegate threads** (T3): one each for theory, Lean and the Rust
  model. A network outage froze all three mid-session; each was
  restarted from its on-disk state.
