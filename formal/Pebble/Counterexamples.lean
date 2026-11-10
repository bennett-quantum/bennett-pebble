import Pebble.Chain

/-! A literal physical wire permutation is not a zero-gate move. -/
namespace Pebble
namespace Counterexamples

def swapWires : Perm Bool :=
  ⟨Bool.not, Bool.not, fun b => by cases b <;> rfl, fun b => by cases b <;> rfl⟩
def differentBits : Symbolic Bool Unit := fun w _ => w

/-- CORE §3 Relabel cannot mean changing physical wire contents with no gates:
identity leaves (0,1) fixed whereas swapping wires produces (1,0). -/
theorem physical_relabel_not_zero_gates :
    ¬ Sound Perm.id differentBits (fun w => differentBits (swapWires.undo w)) := by
  intro h
  have bad := congrFun (h ()) false
  change false = true at bad
  cases bad

/-- The corrected physical operation is sound when represented by its permutation. -/
theorem physical_relabel_with_permutation :
    Sound (Rules.permuteWires swapWires) differentBits
      (fun w => differentBits (swapWires.undo w)) :=
  Rules.wire_relabel_sound swapWires differentBits

/-- The unconditional last clause of CORE 6.2 needs a goal premise:
a zero-length play is legal at T=1 but does not reach T. -/
theorem empty_play_legal_without_goal :
    Chain.Legal 1 0 1 (Chain.start (T := 1) (P := 1) 0) [] (Chain.start 0) ∧
      ¬ Chain.Goal (Chain.start (T := 1) (P := 1) 0) := by
  constructor
  · exact .nil (by decide)
  · intro ⟨s, hs⟩
    have h0 : s = 0 := by apply Fin.ext; omega
    subst s
    simp [Chain.start] at hs

/-- With zero result bits, the empty compute's commit cannot implement payload 1.
This is the oracle-level counterexample to dropping final-result hypotheses. -/
theorem empty_compute_not_one_oracle :
    (oracle (W := Unit) Perm.id (fun (_ : Unit) => ()) (fun (e : Empty) => e.elim)).run
      ⟨(fun _ => false), (fun _ => false), Empty.elim⟩ ≠
      OracleState.mk (fun _ => false) (fun _ => true) Empty.elim := by
  intro h
  have bad := congrArg (fun s => s.target ()) h
  change false = true at bad
  cases bad

end Counterexamples
end Pebble
