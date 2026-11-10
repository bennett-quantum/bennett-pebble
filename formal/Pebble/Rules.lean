import Pebble.Region
import Pebble.Oracle

/-! CORE §3. Width-indexed named values and bundled placements. Rule layout
premises explicitly say how the placement denotation changes; evaluator
specifications are semantic hypotheses, not an assumed trusted optimiser. -/
namespace Pebble
namespace Rules

structure ValueSystem (X : Type) where
  Value : Type
  width : Value → Nat
  denote : (v : Value) → X → Bits (Fin (width v))

structure Binding (V : ValueSystem X) (W : Type) where
  value : V.Value
  bundle : Region (Fin (V.width value)) W

abbrev Placement (V : ValueSystem X) (W : Type) := List (Binding V W)

def denote (V : ValueSystem X) (π : Placement V W) : Symbolic W X :=
  π.foldr (fun b κ => b.bundle.put κ (fun i x => V.denote b.value x i))
    (fun _ _ => false)

/-- Each binding is a complete distinct-wire bundle, disjoint from every other. -/
def Disjoint (b c : Binding V W) : Prop :=
  ∀ i j, b.bundle.wire i ≠ c.bundle.wire j

def WellFormed (π : Placement V W) : Prop := π.Pairwise Disjoint

theorem disjoint_select_none {b c : Binding V W} (h : Disjoint b c)
    (i : Fin (V.width b.value)) : c.bundle.select (b.bundle.wire i) = none := by
  cases hs : c.bundle.select (b.bundle.wire i) with
  | none => rfl
  | some j => exact False.elim (h i j (c.bundle.wire_select _ j hs).symm)

/-- A well-formed placement holds each named value on every one of its bundles. -/
theorem member_content {V : ValueSystem X} {π : Placement V W}
    (wf : WellFormed π) {b : Binding V W} (mem : b ∈ π) :
    b.bundle.read (denote V π) = fun i x => V.denote b.value x i := by
  induction π with
  | nil => cases mem
  | cons c cs ih =>
    have hw := List.pairwise_cons.mp wf
    rcases List.mem_cons.mp mem with hb | hb
    · subst b
      exact Region.read_put _ _ _
    · have hd : Disjoint c b := hw.1 b hb
      have hd' : Disjoint b c := fun i j h => hd j i h.symm
      have ht := ih hw.2 hb
      funext i x
      change c.bundle.put (denote V cs) _ (b.bundle.wire i) x = _
      rw [Region.put, disjoint_select_none hd' i]
      exact congrFun (congrFun ht i) x

/-- Adding a disjoint complete bundle requires no semantic equality decision:
all of its destination wires are clean in the old placement. -/
theorem fresh_clean {V : ValueSystem X} {π : Placement V W} {b : Binding V W}
    (wf : WellFormed (b :: π)) : ∀ i, Clean (denote V π) (b.bundle.wire i) := by
  have disj := (List.pairwise_cons.mp wf).1
  intro i x
  induction π with
  | nil => rfl
  | cons c cs ih =>
    have hd : Disjoint b c := disj c (by simp)
    change c.bundle.put (denote V cs) _ (b.bundle.wire i) x = false
    rw [Region.put, disjoint_select_none hd i]
    apply ih
    · exact List.pairwise_cons.mpr ⟨(fun d hd => disj d (by simp [hd])),
        (List.pairwise_cons.mp (List.pairwise_cons.mp wf).2).2⟩
    · intro d hd
      exact disj d (by simp [hd])

/-- Exact named Eval rule π ↔ π+(Z,v). The evaluator's full-state XOR-write
specification frames every other wire; well-formedness supplies clean Z. -/
theorem eval_add_sound {V : ValueSystem X} (π : Placement V W) (b : Binding V W)
    (wf : WellFormed (b :: π)) (E : Circuit W)
    (readArgs : Bits W → Bits A) (f : Bits A → Bits (Fin (V.width b.value)))
    (evaluator_spec : ∀ s, E.run s = b.bundle.put s
      (xorBits (b.bundle.read s) (f (readArgs s))))
    (meaning : ∀ x, f (readArgs (enc (denote V π) x)) = V.denote b.value x) :
    Sound E (denote V π) (denote V (b :: π)) := by
  intro x
  rw [evaluator_spec, meaning x]
  have hz : b.bundle.read (enc (denote V π) x) = fun _ => false := by
    funext i
    exact fresh_clean wf i x
  rw [hz]
  funext w
  cases hs : b.bundle.select w with
  | none => simp [Region.put, denote, enc, hs, List.foldr]
  | some i =>
    simp only [Region.put, hs, xorBits]
    change xor false (V.denote b.value x i) =
      enc (denote V (b :: π)) x w
    have hout : enc (denote V (b :: π)) x w = V.denote b.value x i := by
      simp [enc, denote, Region.put, hs, List.foldr]
    rw [hout]
    cases V.denote b.value x i <;> rfl

/-- Exact named Copy rule, with membership and disjoint fresh destination checked
as structural premises; an XOR-write copy specification suffices. -/
theorem copy_add_sound {V : ValueSystem X} (π : Placement V W) (v : V.Value)
    (src dst : Region (Fin (V.width v)) W)
    (mem : Binding.mk v src ∈ π) (wf : WellFormed (Binding.mk v dst :: π))
    (E : Circuit W) (copy_spec : ∀ s, E.run s = dst.put s
      (xorBits (dst.read s) (src.read s))) :
    Sound E (denote V π) (denote V (Binding.mk v dst :: π)) := by
  apply eval_add_sound π ⟨v,dst⟩ wf E src.read id copy_spec
  intro x
  have hc := member_content (List.pairwise_cons.mp wf).2 mem
  funext i
  exact congrFun (congrFun hc i) x

/-- Full XOR evaluator specification, including arbitrary destination bits. -/
def XorSpec (E : Circuit (Sum A B)) (f : Bits A → Bits B) : Prop :=
  ∀ a z, E.run (Sum.elim a z) = Sum.elim a (xorBits z (f a))

def evalBefore (u : X → Bits A) : Symbolic (Sum A B) X :=
  Sum.elim (fun a x => u x a) (fun _ _ => false)
def evalAfter (u : X → Bits A) (v : X → Bits B) : Symbolic (Sum A B) X :=
  Sum.elim (fun a x => u x a) (fun b x => v x b)

theorem eval_local {E : Circuit (Sum A B)} {f : Bits A → Bits B}
    (hE : XorSpec E f) (u : X → Bits A) (v : X → Bits B)
    (hv : ∀ x, f (u x) = v x) : Sound E (evalBefore u) (evalAfter u v) := by
  intro x
  have hbefore : enc (evalBefore (B := B) u) x = Sum.elim (u x) (fun _ => false) := by
    funext w; cases w <;> rfl
  rw [hbefore, hE, hv x]
  funext w
  cases w with
  | inl a => rfl
  | inr b => change xor false (v x b) = v x b; cases v x b <;> rfl

/-- CORE's XOR-form evaluators are self-inverse on arbitrary local assignments. -/
theorem xor_evaluator_involution {E : Circuit (Sum A B)} {f : Bits A → Bits B}
    (hE : XorSpec E f) (s : Bits (Sum A B)) : E.run (E.run s) = s := by
  have hs : s = Sum.elim (fun a => s (.inl a)) (fun b => s (.inr b)) := by
    funext w; cases w <;> rfl
  rw [hs, hE, hE, xorBits_cancel]

/-- Bitwise CNOT copy is an explicit self-inverse permutation. -/
def copyRun (s : Bits (Sum A A)) : Bits (Sum A A) :=
  Sum.elim (fun a => s (.inl a)) (fun a => xor (s (.inr a)) (s (.inl a)))

theorem copyRun_involution (s : Bits (Sum A A)) : copyRun (copyRun s) = s := by
  funext w
  cases w with
  | inl a => rfl
  | inr a =>
    change xor (xor (s (.inr a)) (s (.inl a))) (s (.inl a)) = s (.inr a)
    cases s (.inr a) <;> cases s (.inl a) <;> rfl

def copy : Circuit (Sum A A) :=
  ⟨copyRun, copyRun, copyRun_involution, copyRun_involution⟩

theorem copy_spec : XorSpec (copy (A := A)) id := by
  intro a z; rfl

/-- Eval: add a value on clean destinations, with every other physical wire framed. -/
theorem eval_sound {V : ValueSystem X} {v : V.Value} {π π' : Placement V W}
    {E : Circuit (Sum A (Fin (V.width v)))} {f : Bits A → Bits (Fin (V.width v))}
    (R : Region (Sum A (Fin (V.width v))) W) (u : X → Bits A)
    (hE : XorSpec E f) (hv : ∀ x, f (u x) = V.denote v x)
    (hread : R.read (denote V π) = evalBefore u)
    (hlayout : denote V π' = R.put (denote V π) (evalAfter u (V.denote v))) :
    Sound (R.lift E) (denote V π) (denote V π') := by
  rw [hlayout]
  exact R.sound_lift (eval_local hE u (V.denote v) hv) hread

/-- Copy adds a second bundle of the same named value. -/
theorem copy_sound {V : ValueSystem X} {π π' : Placement V W} (v : V.Value)
    (R : Region (Sum (Fin (V.width v)) (Fin (V.width v))) W)
    (hread : R.read (denote V π) = evalBefore (V.denote v))
    (hlayout : denote V π' = R.put (denote V π)
      (evalAfter (V.denote v) (V.denote v))) :
    Sound (R.lift copy) (denote V π) (denote V π') :=
  eval_sound R (V.denote v) copy_spec (fun _ => rfl) hread hlayout

/-- InPlace with residue: the local specification describes the full output,
including stable operands and residue, so it cannot silently discard information. -/
theorem specified_local_sound {V : ValueSystem X} {π π' : Placement V W}
    (R : Region L W) (I : Circuit L) (before after : Symbolic L X)
    (evaluator_spec : ∀ x, I.run (enc before x) = enc after x)
    (hread : R.read (denote V π) = before)
    (hlayout : denote V π' = R.put (denote V π) after) :
    Sound (R.lift I) (denote V π) (denote V π') := by
  rw [hlayout]
  exact R.sound_lift evaluator_spec hread

/-- InPlace, explicitly exposing stable operands, the new value, and residue.
`packIn` includes the clean extension Z; `packOut` includes ALL of the local
output wires. Their concrete wire layouts are supplied as layout certificates. -/
theorem inplace_sound {VS : ValueSystem X} {π π' : Placement VS W}
    (R : Region L W) (I : Circuit L)
    (packIn : Bits U → Bits A → Bits L)
    (packOut : Bits V → Bits Residue → Bits A → Bits L)
    (g : Bits U → Bits A → Bits V × Bits Residue)
    (evaluator_spec : ∀ u a, I.run (packIn u a) = packOut (g u a).1 (g u a).2 a)
    (u : X → Bits U) (a : X → Bits A) (v : X → Bits V) (ρ : X → Bits Residue)
    (meaning : ∀ x, g (u x) (a x) = (v x, ρ x))
    (hread : R.read (denote VS π) = fun w x => packIn (u x) (a x) w)
    (hlayout : denote VS π' = R.put (denote VS π)
      (fun w x => packOut (v x) (ρ x) (a x) w)) :
    Sound (R.lift I) (denote VS π) (denote VS π') := by
  apply specified_local_sound R I _ _ ?_ hread hlayout
  intro x
  change I.run (packIn (u x) (a x)) = packOut (v x) (ρ x) (a x)
  rw [evaluator_spec, meaning x]

/-- Existence of a bijective evaluator forces its complete output (v,residue)
to be injective on the encoded input, without a separate injectivity axiom. -/
theorem inplace_residue_injective (I : Perm A) (pack : U → A) (out : U → A)
    (hpack : ∀ u v, pack u = pack v → u = v)
    (spec : ∀ u, I.run (pack u) = out u) :
    ∀ u v, out u = out v → u = v := by
  intro u v h
  apply hpack u v
  have h' := congrArg I.undo h
  simpa only [← spec, I.undo_run] using h'

/-- Zero-gate Relabel is metadata-only: physical denotations must agree. -/
theorem relabel_sound {V : ValueSystem X} {π π' : Placement V W}
    (h : denote V π = denote V π') : Sound Perm.id (denote V π) (denote V π') := by
  rw [h]; exact sound_id _

/-- An actual wire permutation is also sound, but is a circuit operation. -/
def permuteWires (P : Perm W) : Circuit W where
  run s := s ∘ P.undo
  undo s := s ∘ P.run
  undo_run s := by funext w; simp [Function.comp_def, P.undo_run]
  run_undo s := by funext w; simp [Function.comp_def, P.run_undo]

theorem wire_relabel_sound (P : Perm W) (κ : Symbolic W X) :
    Sound (permuteWires P) κ (fun w => κ (P.undo w)) := fun _ => rfl

/-- Guard includes the disjoint-control obligation (preservation on ALL states). -/
theorem guard_sound {U : Circuit W} {κ κ' : Symbolic W X}
    (h : Sound U κ κ') (p : W) (hp : Preserves U p) :
    Sound (guard p U hp) κ (guardedState (κ p) κ κ') := sound_guard h p hp

/-- Derivations may use any verified primitive, either direction, and composition. -/
inductive Derivation : Symbolic W X → Symbolic W X → Circuit W → Prop
  | primitive {κ κ' U} (h : Sound U κ κ') : Derivation κ κ' U
  | refl (κ) : Derivation κ κ Perm.id
  | reverse {κ κ' U} : Derivation κ κ' U → Derivation κ' κ U.inv
  | seq {κ κ' κ'' U V} : Derivation κ κ' U → Derivation κ' κ'' V →
      Derivation κ κ'' (U.seq V)

/-- CORE 3.2, after discharging the primitive specifications above. -/
theorem calculus_sound {κ κ' : Symbolic W X} {U : Circuit W}
    (d : Derivation κ κ' U) : Sound U κ κ' := by
  induction d with
  | primitive h => exact h
  | refl κ => exact sound_id κ
  | reverse _ ih => exact sound_inverse ih
  | seq _ _ ih₁ ih₂ => exact sound_comp ih₁ ih₂

end Rules
end Pebble
