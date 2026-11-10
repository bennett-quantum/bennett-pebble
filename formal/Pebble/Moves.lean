import Std

/-! CORE §2: permutations, symbolic states, sound moves, frame and controls.
No gate synthesis assumption is needed for these semantic theorems. -/
namespace Pebble

universe u v z

/-- A bijection with its explicit inverse. `seq` below uses execution order. -/
structure Perm (A : Type u) where
  run : A → A
  undo : A → A
  undo_run : ∀ a, undo (run a) = a
  run_undo : ∀ a, run (undo a) = a

namespace Perm
variable {A : Type u}
def id : Perm A := ⟨fun a => a, fun a => a, fun _ => rfl, fun _ => rfl⟩
def inv (U : Perm A) : Perm A := ⟨U.undo, U.run, U.run_undo, U.undo_run⟩
def seq (U V : Perm A) : Perm A where
  run a := V.run (U.run a)
  undo a := U.undo (V.undo a)
  undo_run a := by rw [V.undo_run, U.undo_run]
  run_undo a := by rw [U.run_undo, V.run_undo]

/-- Extend a permutation by an untouched external register. -/
def onSecond {B : Type v} (U : Perm A) : Perm (B × A) where
  run s := (s.1, U.run s.2)
  undo s := (s.1, U.undo s.2)
  undo_run s := by cases s; simp [U.undo_run]
  run_undo s := by cases s; simp [U.run_undo]

/-- A fresh external control; both branches preserve the control. -/
def controlled (U : Perm A) : Perm (Bool × A) where
  run s := (s.1, if s.1 then U.run s.2 else s.2)
  undo s := (s.1, if s.1 then U.undo s.2 else s.2)
  undo_run s := by cases s with | mk b a => cases b <;> simp [U.undo_run]
  run_undo s := by cases s with | mk b a => cases b <;> simp [U.run_undo]
end Perm

abbrev Bits (W : Type u) := W → Bool
abbrev Circuit (W : Type u) := Perm (Bits W)
abbrev Symbolic (W : Type u) (X : Type v) := W → X → Bool

def enc (κ : Symbolic W X) (x : X) : Bits W := fun w => κ w x
def Clean (κ : Symbolic W X) (w : W) : Prop := ∀ x, κ w x = false
def Constant (κ : Symbolic W X) (w : W) : Prop := ∃ b, ∀ x, κ w x = b

/-- CORE's non-clean scratch count. Supply a duplicate-free enumeration of just
scratch wires. Equality of symbolic functions is intentionally not decidable. -/
noncomputable def symbolicSpace (scratch : List W) (κ : Symbolic W X) : Nat := by
  classical
  exact (scratch.filter (fun w => ¬ Clean κ w)).length

/-- The circuit acts only on scratch-plus-input wires; interfaces are framed later. -/
def Sound (U : Circuit W) (κ κ' : Symbolic W X) : Prop :=
  ∀ x, U.run (enc κ x) = enc κ' x

theorem sound_id (κ : Symbolic W X) : Sound Perm.id κ κ := fun _ => rfl

theorem sound_comp {κ κ' κ'' : Symbolic W X} {U V : Circuit W}
    (hU : Sound U κ κ') (hV : Sound V κ' κ'') :
    Sound (U.seq V) κ κ'' := by
  intro x
  change V.run (U.run (enc κ x)) = _
  rw [hU, hV]

theorem sound_inverse {κ κ' : Symbolic W X} {U : Circuit W}
    (h : Sound U κ κ') : Sound U.inv κ' κ := by
  intro x
  change U.undo (enc κ' x) = _
  rw [← h x, U.undo_run]

/-- An explicit partition of wires into active and frame wires. -/
def frame (U : Circuit A) : Circuit (Sum A B) where
  run s := Sum.elim (U.run (fun a => s (.inl a))) (fun b => s (.inr b))
  undo s := Sum.elim (U.undo (fun a => s (.inl a))) (fun b => s (.inr b))
  undo_run s := by
    funext w; cases w with
    | inl a => exact congrFun (U.undo_run (fun a => s (.inl a))) a
    | inr b => rfl
  run_undo s := by
    funext w; cases w with
    | inl a => exact congrFun (U.run_undo (fun a => s (.inl a))) a
    | inr b => rfl

theorem sound_frame {U : Circuit A} {κ κ' : Symbolic A X}
    (h : Sound U κ κ') (φ : Symbolic B X) :
    Sound (frame U) (Sum.elim κ φ) (Sum.elim κ' φ) := by
  intro x
  funext w
  cases w with
  | inl a => exact congrFun (h x) a
  | inr b => rfl

/-- Required for a reversible wire-controlled operation: U never changes p. -/
def Preserves (U : Circuit W) (p : W) : Prop := ∀ s, U.run s p = s p

theorem preserves_inverse {U : Circuit W} {p : W} (h : Preserves U p) :
    Preserves U.inv p := by
  intro s
  have hp := h (U.undo s)
  rw [U.run_undo] at hp
  exact hp.symm

def guard (p : W) (U : Circuit W) (h : Preserves U p) : Circuit W where
  run s := if s p then U.run s else s
  undo s := if s p then U.undo s else s
  undo_run s := by
    have hi : ∀ s, U.undo s p = s p := preserves_inverse h
    cases hs : s p <;> simp [hs, h s, U.undo_run]
  run_undo s := by
    have hi : ∀ s, U.undo s p = s p := preserves_inverse h
    cases hs : s p <;> simp [hs, hi s, U.run_undo]

def guardedState (π : X → Bool) (κ κ' : Symbolic W X) : Symbolic W X :=
  fun w x => if π x then κ' w x else κ w x

theorem sound_guard {U : Circuit W} {κ κ' : Symbolic W X}
    (h : Sound U κ κ') (p : W) (hp : Preserves U p) :
    Sound (guard p U hp) κ (guardedState (κ p) κ κ') := by
  intro x
  change (if κ p x then U.run (enc κ x) else enc κ x) = _
  cases hx : κ p x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    funext w; simp [enc, guardedState, hx]
  · simp only [↓reduceIte]
    rw [h x]
    funext w; simp [enc, guardedState, hx]

/-- CORE 2.4: a zero control permits deletion on this symbolic state. -/
theorem stage_zero {U : Circuit W} {κ : Symbolic W X} {p : W}
    (hp : Preserves U p) (hc : Clean κ p) :
    Sound (guard p U hp) κ κ := by
  intro x
  simp [guard, enc, hc x]

/-- Deleting a zero-controlled gate preserves the exact postcondition, in both directions. -/
theorem stage_zero_delete {U : Circuit W} {κ κ' : Symbolic W X} {p : W}
    (hp : Preserves U p) (hc : Clean κ p) :
    Sound (guard p U hp) κ κ' ↔ Sound Perm.id κ κ' := by
  constructor
  · intro h x
    exact ((stage_zero hp hc) x).symm.trans (h x)
  · intro h x
    exact ((stage_zero hp hc) x).trans (h x)

/-- CORE 2.4: a one control permits removal of that control. -/
theorem stage_one {U : Circuit W} {κ κ' : Symbolic W X} {p : W}
    (hp : Preserves U p) (hc : ∀ x, κ p x = true) :
    Sound (guard p U hp) κ κ' ↔ Sound U κ κ' := by
  simp only [Sound, guard, enc, hc, ↓reduceIte]

/-- A local replacement may be surrounded by arbitrary sound prefix/suffix moves. -/
theorem sound_replacement {κ₀ κ₁ κ₂ κ₃ : Symbolic W X} {P U V Q : Circuit W}
    (hP : Sound P κ₀ κ₁) (hU : Sound U κ₁ κ₂)
    (hV : ∀ x, V.run (enc κ₁ x) = U.run (enc κ₁ x)) (hQ : Sound Q κ₂ κ₃) :
    Sound ((P.seq V).seq Q) κ₀ κ₃ :=
  sound_comp (sound_comp hP (fun x => (hV x).trans (hU x))) hQ

end Pebble
