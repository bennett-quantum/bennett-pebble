import Pebble.Chain
import Pebble.Checker
import Pebble.Counterexamples
import Pebble.DAG
import Pebble.Examples
import Pebble.Moves
import Pebble.Oracle
import Pebble.Region
import Pebble.Rules

/-! All named theorems, including helpers, are audited. -/
#print axioms Pebble.Chain.state_setStep
#print axioms Pebble.Chain.adv_sound
#print axioms Pebble.Chain.ret_sound
#print axioms Pebble.Chain.state_copy_update
#print axioms Pebble.Chain.dup_sound
#print axioms Pebble.Chain.undup_sound
#print axioms Pebble.Chain.move_sound
#print axioms Pebble.Chain.legal_play_sound
#print axioms Pebble.Chain.legal_play_derivation
#print axioms Pebble.Chain.start_clean
#print axioms Pebble.Chain.legal_play_oracle
#print axioms Pebble.Chain.checker_sound
#print axioms Pebble.Chain.checker_complete
#print axioms Pebble.Chain.accepts_iff_legal
#print axioms Pebble.Chain.legal_peak_bound
#print axioms Pebble.Chain.checker_peak_bound
#print axioms Pebble.Chain.checked_play_oracle
#print axioms Pebble.Counterexamples.physical_relabel_not_zero_gates
#print axioms Pebble.Counterexamples.physical_relabel_with_permutation
#print axioms Pebble.Counterexamples.empty_play_legal_without_goal
#print axioms Pebble.Counterexamples.empty_compute_not_one_oracle
#print axioms Pebble.DAG.toggle_sound
#print axioms Pebble.DAG.strategy_sound
#print axioms Pebble.DAG.strategy_derivation
#print axioms Pebble.sound_id
#print axioms Pebble.sound_comp
#print axioms Pebble.sound_inverse
#print axioms Pebble.sound_frame
#print axioms Pebble.preserves_inverse
#print axioms Pebble.sound_guard
#print axioms Pebble.stage_zero
#print axioms Pebble.stage_zero_delete
#print axioms Pebble.stage_one
#print axioms Pebble.sound_replacement
#print axioms Pebble.xorBits_cancel
#print axioms Pebble.commit_involution
#print axioms Pebble.oracle_contract
#print axioms Pebble.oracle_involution
#print axioms Pebble.oracle_controlled
#print axioms Pebble.oracle_garbage_independent
#print axioms Pebble.dirty_oracle_contract
#print axioms Pebble.borrowed_oracle_contract
#print axioms Pebble.clean_oracle_contract
#print axioms Pebble.Region.read_put
#print axioms Pebble.Region.put_read
#print axioms Pebble.Region.put_put
#print axioms Pebble.Region.sound_lift
#print axioms Pebble.Rules.disjoint_select_none
#print axioms Pebble.Rules.member_content
#print axioms Pebble.Rules.fresh_clean
#print axioms Pebble.Rules.eval_add_sound
#print axioms Pebble.Rules.copy_add_sound
#print axioms Pebble.Rules.eval_local
#print axioms Pebble.Rules.xor_evaluator_involution
#print axioms Pebble.Rules.copyRun_involution
#print axioms Pebble.Rules.copy_spec
#print axioms Pebble.Rules.eval_sound
#print axioms Pebble.Rules.copy_sound
#print axioms Pebble.Rules.specified_local_sound
#print axioms Pebble.Rules.inplace_sound
#print axioms Pebble.Rules.inplace_residue_injective
#print axioms Pebble.Rules.relabel_sound
#print axioms Pebble.Rules.wire_relabel_sound
#print axioms Pebble.Rules.guard_sound
#print axioms Pebble.Rules.calculus_sound

-- This noncomputable definition uses standard classical decidability.
#print axioms Pebble.symbolicSpace
