# Pebble: basis-state mechanisation

This Lake project checks the architectural soundness argument in
[`docs/CORE.md`](../docs/CORE.md): local sound compute moves compose, and a
compute/commit/uncompute sandwich implements the oracle contract regardless of
the schedule and of non-result garbage. It includes sound named rules, a finite
DAG pebbling game, an allocated chain game, and a verified executable checker.
The end-to-end theorem is conditional on local evaluator specifications and on
`σ_T` containing the desired reference-function results. It does **not** prove
that a Bennett interpreter or GBM computes those results.

Only `formal/` was written. No repository was created and no commits were made.
Neither CORE nor the concurrent theory/model tracks were edited.

## Build and inspect

Requires the installed Lean **4.35.0**, Lake **5.0.0**, and their bundled `Std`.
There are **no package dependencies and no Mathlib**. `lean-toolchain` pins the
version, and `lake-manifest.json` contains no external packages. From this
workspace, or a fresh copy of these source files:

```sh
cd formal
~/.elan/bin/lake build
~/.elan/bin/lake env lean Pebble/Audit.lean
```

The default library target imports every module, the regression examples, and
`Audit.lean`. The audit runs `#print axioms` on **all 65 named theorems**, including
helpers, rather than only the headline theorems. It additionally audits the
noncomputable symbolic-space definition. There are no `sorry`, `admit`, custom
axiom declarations, unsafe proofs, or native-decision proof shortcuts. Standard
Lean logical axioms are distinguished from added axioms below.

Useful entry points:

- [`Moves.lean`](Pebble/Moves.lean): permutation and symbolic semantics, move algebra, staging.
- [`Region.lean`](Pebble/Region.lean): explicit wire bundles and their frame extension.
- [`Oracle.lean`](Pebble/Oracle.lean): compute/commit/uncompute, controls, and dirty borrowing.
- [`Rules.lean`](Pebble/Rules.lean): named placements and rule soundness.
- [`DAG.lean`](Pebble/DAG.lean): finite DAG, validity, and strategy compilation.
- [`Chain.lean`](Pebble/Chain.lean): allocated chain moves and end-to-end soundness.
- [`Checker.lean`](Pebble/Checker.lean): executable replay and verified statistics.
- [`Counterexamples.lean`](Pebble/Counterexamples.lean): precise qualifications of CORE.
- [`Examples.lean`](Pebble/Examples.lean): kernel-checked executable examples.
- [`Audit.lean`](Pebble/Audit.lean): complete axiom audit.

## Statement map

Names in the next table are in namespace `Pebble` unless prefixed otherwise.
Every named theorem, including the supporting lemmas, is accounted for here or
in the helper table immediately below.

| CORE statement | Lean definitions / theorems | Precise content |
|---|---|---|
| Setting; Definitions 2.1–2.2 | `Perm`, `Bits`, `Circuit`, `Symbolic`, `enc`, `Clean`, `Constant`, `symbolicSpace`, `Sound`, `initial` | Bit assignments, symbolic evaluation, bijections with explicit two-sided inverses, and universal basis-state soundness. |
| Lemma 2.3(a) | `sound_comp` | Execution-order `U.seq V` is mathematical `VU`. |
| Lemma 2.3(b) | `sound_inverse` | Reverse a sound move using its explicit inverse. |
| Lemma 2.3(c) | `sound_frame`, `Region.sound_lift` | Disjoint-sum frame and selected-region frame, with arbitrary outside contents. |
| Lemma 2.3(d) | `sound_guard` | A preserved control wire selects the post-state pointwise in the environment. |
| Lemma 2.4 | `stage_zero`, `stage_zero_delete`, `stage_one`, `sound_replacement` | A zero-controlled gate is identity at this symbolic state; deletion preserves any postcondition. A one-controlled gate is equivalent to its uncontrolled body. Local replacements compose with arbitrary sound prefix/suffix. |
| Theorem 2.5, contract | `oracle_contract`, `clean_oracle_contract` | Arbitrary target/fault bits; all initial work restored; the second theorem explicitly displays zero scratch. |
| Theorem 2.5(i) | `oracle_involution` | Stronger: involution on **every** work/target/fault assignment, not only the clean domain. |
| Theorem 2.5(ii) | `controlCommitOnly`, `oracle_controlled` | Stronger: controlling only commit equals controlling the whole sandwich on **every** assignment, for a fresh external bit. |
| Theorem 2.5(iii) | `oracle_garbage_independent` | Two different computes with equal result projections implement identical clean-domain oracles, regardless of all other final work bits. |
| Theorem 2.5, dirty extension | `borrowed_oracle_contract`, `dirty_oracle_contract` | Untouched dirty frame, and more generally compute allowed to use dirty wires provided the result specification holds for **every** dirty assignment. |
| Definition 3.1 | `Rules.ValueSystem`, `Binding`, `Placement`, `denote`, `WellFormed` | Width-indexed named bitvectors, complete injective bundles, pairwise-disjoint finite placements, zero elsewhere. |
| Theorem 3.2, Eval | `Rules.eval_add_sound`, `eval_sound` | Exact placement addition on a fresh bundle, and a local-evaluator/frame version. The XOR evaluator specification and denotation relation are explicit hypotheses. |
| Theorem 3.2, Copy | `Rules.copy_add_sound`, `copy_sound` | Exact named-placement Copy given its XOR-write specification; also a concrete self-inverse bitwise CNOT implementation in a selected two-bundle region. |
| Theorem 3.2, InPlace with residue | `Rules.inplace_sound`, `inplace_residue_injective` | Explicit old value, stable operands, new value, residue, and complete input/output layouts. A specified bijective evaluator gives soundness; injective input packing forces injectivity of its complete encoded output. |
| Theorem 3.2, Relabel | `Rules.relabel_sound`, `wire_relabel_sound` | Zero-gate metadata relabel needs unchanged physical denotation. A physical wire permutation is sound as an actual permutation operation. See the qualification below. |
| Theorem 3.2, Guard | `Rules.guard_sound` | Conditional symbolic outputs, including zero/old-value false branches, using a control preserved on all assignments. |
| Theorem 3.2, derivations | `Rules.Derivation`, `calculus_sound` | Verified primitives, identity, inverse and sequential composition preserve soundness. |
| Corollary 3.3 | `DAG.Graph`, `Config`, `Enabled`, `Valid`, `EvalSpec`, `compile`; `toggle_sound`, `strategy_sound`, `strategy_derivation` | Every valid finite add/remove-pebble strategy from inputs-only is sound, and is a composition of primitive derivations ending at exactly its final pebbled set. |
| Definition 6.1 | `Chain.Config`, `Move`, `Enabled`, `applyMove`, `space`, `moveCost`, `start`, `Goal`, `Legal` | Allocated tokens, one residue per index, the four reversible moves, capacity checked at all states, and game costs. |
| Theorem 6.2, local steps | `Chain.adv_sound`, `ret_sound`, `dup_sound`, `undup_sound`, `move_sound` | Step soundness is hypothesised **only on one local token plus its residue**. Framing and inverses derive the full-state moves; copying is proved directly. |
| Theorem 6.2, plays | `Chain.legal_play_sound`, `legal_play_derivation` | Any legal allocated play is sound, from any configuration. No strategy shape, optimality or halting argument is assumed. |
| Theorem 6.2 + Theorem 2.5 | `Chain.start_clean`, `legal_play_oracle` | Any legal play from the single initial token reaching a specified token at `T` gives the full oracle contract, if the designated bits of `σ_T` are payload/code. |
| Requested checker extension | `Chain.checker_sound`, `checker_complete`, `accepts_iff_legal`, `checker_peak_bound`, `checked_play_oracle` | Executable acceptance is equivalent to allocated legality. It certifies the exact endpoint, exact peak, exact total game cost, capacity bound, and the end-to-end oracle contract. |
| Relabel qualification | `Counterexamples.physical_relabel_not_zero_gates`, `physical_relabel_with_permutation` | A physical swap of `(0,1)` fails as identity, and succeeds as its actual wire permutation. |
| Goal qualification in 6.2 | `Counterexamples.empty_play_legal_without_goal`, `empty_compute_not_one_oracle` | At `T=1`, the empty play is legal but not a goal. An empty compute on zero result bits cannot commit constant payload one. |

Supporting theorems are not additional research assumptions:

| Helper theorem(s) | CORE connection / purpose |
|---|---|
| `sound_id`, `preserves_inverse` | Lemma 2.3: identity move; control remains preserved by the inverse, making guarding a bijection. |
| `xorBits_cancel`, `commit_involution` | Theorem 2.5: XOR cancellation and the involutive commit. |
| `Region.read_put`, `put_read`, `put_put` | Lemma 2.3(c): read/write laws proving selected-region lifting is a bijection. |
| `Rules.disjoint_select_none`, `member_content`, `fresh_clean` | Definition 3.1: disjoint bundles do not alias, membership gives its value, and fresh destinations are clean. |
| `Rules.eval_local`, `xor_evaluator_involution`, `copyRun_involution`, `copy_spec` | Theorem 3.2: XOR evaluation on clean targets and the global self-inverse laws/specifications for Eval and Copy. |
| `Rules.specified_local_sound` | Theorem 3.2: reusable local evaluator + layout certificate + frame argument. |
| `Chain.state_setStep`, `state_copy_update` | Theorem 6.2: the configuration update is exactly the corresponding physical bundle write, with its frame intact. |
| `Chain.legal_peak_bound` | Definition 6.1 / checker: every visited configuration contributes at most `S` to the maximum. |

## Modelling choices, strengthenings and limitations

### Basis semantics and wires

1. `Circuit W` means **any** bijection of `W → Bool`, with stored `run`, `undo`
   and two inverse proofs. There is no gate syntax, gate synthesis, generator
   membership, complex vector space, amplitude, phase or linearity development.
   The semantic theorems therefore apply to a larger class than CORE's generated
   circuits, and in particular to its permutation tier. Bitwise commit and Copy
   are constructed explicitly. Mapping abstract evaluators to X/CX/CCX/MCX is a
   separate obligation.
2. General §2 lemmas allow arbitrary wire types, even infinite ones: finiteness
   is unnecessary for the algebra. DAG and chain wire types are finite, using
   `Fin`, products, sums and dependent pairs. Oracle interface wires are separate
   work/target/fault fields, equivalent to a disjoint wire partition; compute
   cannot access target/fault by construction.
3. `X` is an arbitrary type. Classical compilation parameters are absent and
   thus fixed. The reference `F_B` is represented by its two bitvector-valued
   projections `payload` and `code`, with arbitrary independent index types/widths.
   The development assumes no semantics for fault codes or ISA objects.
4. Symbolic states are total on the scratch-plus-input type. `enc` is pointwise
   evaluation. `initial input` partitions work wires as input `I` plus scratch
   `S`, holds `input x` on `I` and zero on `S`. Taking `X := Bits I` and
   `input := id` gives literally the CORE domain `|x⟩|t⟩|f⟩|0…0⟩`; allowing an
   arbitrary input encoding is a generalisation. No injectivity of this encoding
   is needed by the semantic theorem.
5. `symbolicSpace scratch κ` counts non-clean wires in an explicit list of
   scratch wires. To match CORE exactly the caller supplies a duplicate-free,
   exhaustive list excluding inputs. This function is deliberately
   noncomputable: arbitrary function equality is not a decision procedure.
   The executable game space measure is separate.
6. Result bundles are read maps. They need not be injective or mutually
   disjoint, since reading the same computed bit into several separate targets
   is sound. Theorems consequently generalise CORE's usual distinct-bundle
   convention. Target and fault storage remain disjoint from work and from each
   other by the state type.

### Move algebra, staging, oracle and dirty data

7. Frame is supplied as an actual disjoint-sum extension, or a `Region` containing
   an encoder/selector with both coherence laws. These laws imply bundle
   injectivity and ensure exact identity on its complement. An operation merely
   preserving outside outputs but depending on them is not silently treated as
   an independent local circuit.
8. A wire-controlled operation requires `Preserves U p` on **all** assignments.
   CORE's disjoint-support condition implies this; it also allows more general
   preservation than a syntactic support test. That premise constructs a
   reversible controlled circuit rather than assuming it exists.
9. Staging is local at a certified symbolic state. The deletion/removal
   equivalences and replacement theorem justify use inside a sound circuit.
   They do not implement a partial evaluator or justify deleting a wire merely
   because it is constant at one point in its lifetime. Global removal needs all
   uses rewritten and any required interface outputs materialised. The broad
   classical-data consequence in 2.4 is not a proved resource or compiler theorem.
10. `oracle_contract` works for *any* initial symbolic state, and
    `clean_oracle_contract` specialises the exact scratch-zero domain. It has no
    constraint on non-result final wires, nor any requirement that compute has
    cleaned its garbage. Involution and the fresh-control equality are global
    strengthenings. A fresh control is an additional external `Bool`; a tuple of
    inherited controls can be represented by its predicate, but multi-control
    gate synthesis is not provided.
11. Untouched dirty bits are a literal arbitrary frame. The stronger dirty theorem
    lets compute use them and even change them before commit, provided soundness
    and result independence hold uniformly over all dirty assignments. It then
    restores their initial assignment by uncomputation. CORE's identity-on-dirty
    sound moves are a special case. A clean-only specification is insufficient;
    no dirty-wire allocator or borrowing compiler is verified.

### Names, rules and DAG pebbling

12. Named values have dependent widths. A placement is a finite **list** of
    bindings, with `WellFormed` requiring pairwise-disjoint complete bundles;
    each bundle is a `Region`, hence has distinct wires. The list is a convenient
    representation of CORE's finite set. Denotation folds bundle writes over
    zero. It is defined even for malformed lists, but the exact add/copy theorems
    require well-formedness, and `member_content`/`fresh_clean` connect that
    structural condition to physical contents. The generic local rule theorems
    are stronger: any placement denotations satisfying their layout premises
    suffice, whether or not the caller separately proves well-formedness.
13. The exact Eval theorem adds a binding on disjoint clean destination wires;
    its full-state XOR-write evaluator specification frames all other wires.
    The local version uses disjoint argument/output types and a stronger XOR
    specification covering arbitrary target bits. The latter proves global
    self-inversion. Copy has both a specified full-state add theorem and a
    concrete CNOT implementation; its inverse removes a duplicate only while
    another disjoint equal source remains.
14. InPlace makes the complete local input/output layouts explicit as packing
    functions, together with layout/denotation certificates. The output includes
    the residue and stable operands; a full bijective evaluator is a hypothesis,
    so no information can be discarded outside its specified output. The
    development does not infer a bijective evaluator from injectivity of `g`,
    or automatically synthesise/simplify residue. The separate injectivity lemma
    requires injective input packing; it states exactly what follows from an
    existing evaluator. Concrete bundle-size arithmetic, packing injectivity,
    and named layout certificates are caller obligations.
15. Guard is proved on physical symbolic states, selecting post/pre values
    pointwise. Named values for `p ? v : 0` or `p ? v : u` must be available with
    those denotations if this is to be represented by a new named placement.
    There is no decision procedure for equality of arbitrary denotations or for
    verifying arbitrary evaluator code. `Derivation.primitive` contains a proof
    of soundness; the rule lemmas construct such proofs. The chain checker below
    avoids denotation equality by relying once on local step certificates.
16. DAG vertices are `Fin n`, with variable-width values and one fixed physical
    bundle per vertex. Parents have strictly smaller indices (a supplied
    topological numbering), and input vertices have no parents. Initially exactly
    input vertices are pebbled; they cannot be toggled. A legal move toggles any
    non-input vertex when all parents are pebbled. The graph rank restriction is
    not needed in the soundness induction itself. Parent/value semantics are
    provided by `EvalSpec`, which asserts XOR into arbitrary target contents
    whenever parent bundles are correct. Both adding and removing a pebble use
    that same XOR evaluator. There is no DAG strategy optimiser, memory bound,
    or game-completeness/optimality result. `strategy_derivation` actually
    composes one certified primitive per move.

### Chain refinement and executable checking

17. Tokens have explicit distinct physical slots `Fin P` with optional positions
    `Fin (T+1)`. Residues have one physical bundle at each `Fin T`. Forgetting slot
    identities yields CORE's multiset/set interpretation. `Dup` specifies its
    source and a free destination; `Undup` requires two **distinct**, equal tokens
    and clears the destination. This makes “remove a duplicate” precise and
    excludes erasing the last copy. `Adv`/`Ret` change a selected token and the
    unique corresponding residue exactly as in CORE. Reaching `T` requires a
    chosen final result slot; a `Goal` witness supplies one.
18. **Scope of the chain theorem:** every legal **allocated** play is covered.
    There is no mechanised theorem allocating an arbitrary unlabelled multiset
    strategy, or proving allocation completeness for a fixed `P`. An unlabelled
    finite play must first be annotated with slot choices and enough slots;
    exhaustion is a checker rejection. This is an explicit refinement of 6.1,
    not a proof about a scheduler that supplies no wire allocation. No strategy
    restrictions beyond that refinement are imposed.
19. `space = m * occupiedSlots + r * liveResidues` is exactly the game's charge
    on these configurations, including input-token space. It is **not** asserted
    equal to `symbolicSpace`: named values can have identically zero bits. The
    fixed semantic wire universe reserves `P*m + T*r` wires; the live-space charge
    regards free slots and absent residues as clean/free storage. Dynamic physical
    reuse of distinct dead residue bundles, evaluator-internal peak scratch,
    concrete hardware qubit count and gate-count accounting are not verified.
    In particular, no scalability or `O(log T)` representation claim follows
    from the static semantic wire universe or this list checker.
20. The only chain evaluator hypothesis is `StepSound`: one local move
    `(σ_j,0) → (σ_(j+1),ρ_j)`, with fixed widths `m,r`, for each time index. Ret
    uses its explicit inverse. Copy is constructed, so a sound-copy hypothesis
    is unnecessary. The rest of the physical state is framed using proved region
    laws. There are no global “all moves are sound” scheduler assumptions.
21. The initial token contains `σ₀(x)` and every other token/residue wire is zero
    (`start_clean`). This is the initial input bundle at the chain layer; if a
    concrete machine state also has clean fields inside `σ₀`, that fact comes
    from its encoding. The oracle restores **all** these work/input bits. The
    conclusion requires correct projections of `σ_T`; it says nothing about the
    ISA function until those semantic hypotheses have been discharged.
22. The checker takes a typed expanded list of moves. Out-of-range indices cannot
    be constructed as `Fin` values; there is no untrusted text/JSON parser here.
    It checks the starting, intermediate and final capacity bounds and every
    enabling condition. `none` means reject; `some Report` contains the endpoint,
    peak and cost. `accepts` is the requested Boolean facade. Statistics are
    proved equal to independent structural specifications `replay`, `peakSpace`,
    and `totalCost`, not merely stored alongside legality. Acceptance is also
    complete for this allocated legality relation. A successful check need not
    reach a goal: the oracle theorem separately requires a token at `T`.
23. The checker is executable without classical choice; it scans finite slot and
    residue lists to compute each space charge. No linear-time-in-description
    complexity theorem is proved, and it does not replay compressed repetitions,
    shared circuit DAGs or billion-step schedules efficiently. Costs are the
    arbitrary natural parameters `a,k`, not a proved emitted-gate cost.

## Qualifications and counterexamples to literal readings of CORE

**Relabel.** A zero-gate relabel is sound when it changes names or bundle order
without changing any physical wire's denotation. Reading “`I_g` a wire
permutation; none (zero gates)” as an actual state-changing wire permutation
would be false. With two wires holding `(0,1)`, a swap should yield `(1,0)`,
but identity leaves `(0,1)`. `physical_relabel_not_zero_gates` machine-checks
this counterexample. The corrected alternatives are `relabel_sound` (unchanged
physical denotation, identity circuit) and `wire_relabel_sound` (actual physical
permutation circuit). This disambiguates metadata rewiring from moving contents;
it does not claim metadata relabelling itself needs gates.

**A goal is necessary in 6.2.** The unconditional phrase “every legal play …
hence … yields a correct oracle” is false unless goal attainment and the result
specification are understood. At `T=1`, the zero-length play is legal but has
no token at `1` (`empty_play_legal_without_goal`). If the initial result bit is
zero and the desired payload is constant one, its empty compute's sandwich
cannot be that oracle (`empty_compute_not_one_oracle`). The corrected theorem
is `legal_play_oracle`: legal play **plus** a token at `T` **plus** the two final
result-projection equations. This is the goal-qualified reading requested for
this track.

**“Correct iff a composition of sound moves.”** The proved architectural result
is the soundness direction: certified rules / an accepted legal play ending in
the right projections give a correct oracle. The checker has its own precise
`accepts_iff_legal` theorem. No completeness theorem says that all correct
circuits or all useful optimisations are expressible by a fixed named calculus.
The semantic existential reading is different: every intermediate circuit
already induces some symbolic functions. No counterexample to that existential
reading is claimed. The prose's “iff” is therefore not used as a named-calculus
completeness assumption.

## Not mechanised

- Reference ISA/interpreter semantics, budget truncation, GBM simulation,
  predecessor-rank construction, classical reachability and the identification
  of `σ_T` with `F_B` (§§4–5): these need a separate machine model; step and
  function specifications are hypotheses here.
- Concrete arithmetic/shift/select evaluators, the residue table and residue
  minimisation (§3.4): the general evaluator-with-residue rule is checked, but
  no particular ISA arithmetic implementation is supplied.
- Unlabelled-to-allocated chain-play completeness, optimal schedules, lower
  bounds, recurrences, non-uniform games and compact strategy descriptions
  (§6.3): this track proves schedule soundness, not scheduler optimality.
- A syntactic checker for arbitrary named rules or emitted gate programs:
  arbitrary function equality is undecidable. Only the allocated chain-game
  checker is executable and verified; evaluator specifications remain proof
  obligations.
- Physical allocation/reuse, exact gate counts, peak circuit workspace,
  hierarchical circuit costing/emission and streaming complexity (§7): abstract
  permutations have no such syntax or cost semantics.
- Hilbert-space linear extension, phases, measurements, ghost pebbles and
  quantum superposition proofs (§8): the requested scope is basis permutations.
  Memory lowering, address decoding, and a dirty-borrowing implementation are
  likewise not modelled, although the general frame/dirty semantic theorems apply.
- The global partial-evaluation/classical-data resource conclusion of Lemma 2.4:
  local staging rewrites are proved; a whole compiler and its resource analysis
  are absent.

## Validation and axiom audit

`Examples.lean` checks all four chain moves in one play, a final token at `T`,
exact peak `3` and cost `32` at `a=7,k=2`, rejection at capacity `2`, rejection
of residue overwrite, and rejection of erasing the only token. These are
kernel computations via `decide` in addition to the general proofs.

The final clean build and complete `#print axioms` output are recorded below.
`propext` and `Quot.sound` are Lean's standard logical axioms (function
extensionality uses the latter). The noncomputable `symbolicSpace` definition
also uses standard `Classical.choice`; it is not used by the executable checker
or by any of the named theorems. There are no project-added axioms or proof holes.

### Final clean build result

Run from `formal/`, with both commands exiting **0**:

```sh
~/.elan/bin/lake clean
~/.elan/bin/lake build
```

The following is the complete captured build output, including every
`#print axioms` result. The same transcript is [final-build.log](final-build.log).
The separately rerun audit also exited **0**; its raw output, without Lake's
source-location prefixes, is [axioms.txt](axioms.txt).

```text
✔ [2/13] Built Pebble.Moves (1.1s)
✔ [3/13] Built Pebble.Region (815ms)
✔ [4/13] Built Pebble.Oracle (1.2s)
✔ [5/13] Built Pebble.Rules (1.0s)
✔ [6/13] Built Pebble.DAG (844ms)
✔ [7/13] Built Pebble.Chain (1.9s)
✔ [8/13] Built Pebble.Counterexamples (700ms)
✔ [9/13] Built Pebble.Checker (1.1s)
✔ [10/13] Built Pebble.Examples (684ms)
ℹ [11/13] Built Pebble.Audit (686ms)
info: Pebble/Audit.lean:12:0: 'Pebble.Chain.state_setStep' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:13:0: 'Pebble.Chain.adv_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:14:0: 'Pebble.Chain.ret_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:15:0: 'Pebble.Chain.state_copy_update' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:16:0: 'Pebble.Chain.dup_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:17:0: 'Pebble.Chain.undup_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:18:0: 'Pebble.Chain.move_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:19:0: 'Pebble.Chain.legal_play_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:20:0: 'Pebble.Chain.legal_play_derivation' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:21:0: 'Pebble.Chain.start_clean' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:22:0: 'Pebble.Chain.legal_play_oracle' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:23:0: 'Pebble.Chain.checker_sound' depends on axioms: [propext]
info: Pebble/Audit.lean:24:0: 'Pebble.Chain.checker_complete' depends on axioms: [propext]
info: Pebble/Audit.lean:25:0: 'Pebble.Chain.accepts_iff_legal' depends on axioms: [propext]
info: Pebble/Audit.lean:26:0: 'Pebble.Chain.legal_peak_bound' depends on axioms: [propext]
info: Pebble/Audit.lean:27:0: 'Pebble.Chain.checker_peak_bound' depends on axioms: [propext]
info: Pebble/Audit.lean:28:0: 'Pebble.Chain.checked_play_oracle' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:29:0: 'Pebble.Counterexamples.physical_relabel_not_zero_gates' does not depend on any axioms
info: Pebble/Audit.lean:30:0: 'Pebble.Counterexamples.physical_relabel_with_permutation' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:31:0: 'Pebble.Counterexamples.empty_play_legal_without_goal' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:32:0: 'Pebble.Counterexamples.empty_compute_not_one_oracle' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:33:0: 'Pebble.DAG.toggle_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:34:0: 'Pebble.DAG.strategy_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:35:0: 'Pebble.DAG.strategy_derivation' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:36:0: 'Pebble.sound_id' does not depend on any axioms
info: Pebble/Audit.lean:37:0: 'Pebble.sound_comp' does not depend on any axioms
info: Pebble/Audit.lean:38:0: 'Pebble.sound_inverse' does not depend on any axioms
info: Pebble/Audit.lean:39:0: 'Pebble.sound_frame' depends on axioms: [Quot.sound]
info: Pebble/Audit.lean:40:0: 'Pebble.preserves_inverse' does not depend on any axioms
info: Pebble/Audit.lean:41:0: 'Pebble.sound_guard' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:42:0: 'Pebble.stage_zero' depends on axioms: [propext]
info: Pebble/Audit.lean:43:0: 'Pebble.stage_zero_delete' depends on axioms: [propext]
info: Pebble/Audit.lean:44:0: 'Pebble.stage_one' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:45:0: 'Pebble.sound_replacement' does not depend on any axioms
info: Pebble/Audit.lean:46:0: 'Pebble.xorBits_cancel' depends on axioms: [Quot.sound]
info: Pebble/Audit.lean:47:0: 'Pebble.commit_involution' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:48:0: 'Pebble.oracle_contract' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:49:0: 'Pebble.oracle_involution' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:50:0: 'Pebble.oracle_controlled' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:51:0: 'Pebble.oracle_garbage_independent' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:52:0: 'Pebble.dirty_oracle_contract' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:53:0: 'Pebble.borrowed_oracle_contract' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:54:0: 'Pebble.clean_oracle_contract' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:55:0: 'Pebble.Region.read_put' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:56:0: 'Pebble.Region.put_read' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:57:0: 'Pebble.Region.put_put' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:58:0: 'Pebble.Region.sound_lift' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:59:0: 'Pebble.Rules.disjoint_select_none' does not depend on any axioms
info: Pebble/Audit.lean:60:0: 'Pebble.Rules.member_content' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:61:0: 'Pebble.Rules.fresh_clean' depends on axioms: [propext]
info: Pebble/Audit.lean:62:0: 'Pebble.Rules.eval_add_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:63:0: 'Pebble.Rules.copy_add_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:64:0: 'Pebble.Rules.eval_local' depends on axioms: [Quot.sound]
info: Pebble/Audit.lean:65:0: 'Pebble.Rules.xor_evaluator_involution' depends on axioms: [Quot.sound]
info: Pebble/Audit.lean:66:0: 'Pebble.Rules.copyRun_involution' depends on axioms: [Quot.sound]
info: Pebble/Audit.lean:67:0: 'Pebble.Rules.copy_spec' depends on axioms: [Quot.sound]
info: Pebble/Audit.lean:68:0: 'Pebble.Rules.eval_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:69:0: 'Pebble.Rules.copy_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:70:0: 'Pebble.Rules.specified_local_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:71:0: 'Pebble.Rules.inplace_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:72:0: 'Pebble.Rules.inplace_residue_injective' does not depend on any axioms
info: Pebble/Audit.lean:73:0: 'Pebble.Rules.relabel_sound' does not depend on any axioms
info: Pebble/Audit.lean:74:0: 'Pebble.Rules.wire_relabel_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:75:0: 'Pebble.Rules.guard_sound' depends on axioms: [propext, Quot.sound]
info: Pebble/Audit.lean:76:0: 'Pebble.Rules.calculus_sound' does not depend on any axioms
info: Pebble/Audit.lean:79:0: 'Pebble.symbolicSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
✔ [12/13] Built Pebble (563ms)
Build completed successfully (13 jobs).
```

The source scan found no `sorry`, `admit`, `sorryAx`, custom `axiom` declarations
or `unsafe` declarations in the 11 Lean source files. The audit contains no
`sorryAx`; the package manifest has `packages: []`. The 65 theorem audit commands
cover all named theorems in the development; the 66th command audits
`symbolicSpace`. All six regression examples are included in the clean build.
