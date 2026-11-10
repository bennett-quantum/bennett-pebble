import Pebble.Moves

/-! Explicit disjoint wire bundles. A selector supplies the partition required
by the frame rule, without finite search or a classical choice operation. -/
namespace Pebble

structure Region (A W : Type) where
  wire : A → W
  select : W → Option A
  select_wire : ∀ a, select (wire a) = some a
  wire_select : ∀ w a, select w = some a → wire a = w

namespace Region
variable {A W D X : Type} (R : Region A W)

def read (s : W → D) : A → D := fun a => s (R.wire a)
def put (s : W → D) (v : A → D) : W → D := fun w =>
  match R.select w with
  | some a => v a
  | none => s w

@[simp] theorem read_put (s : W → D) (v : A → D) : R.read (R.put s v) = v := by
  funext a; simp [read, put, R.select_wire]

@[simp] theorem put_read (s : W → D) : R.put s (R.read s) = s := by
  funext w
  cases h : R.select w with
  | none => simp [put, h]
  | some a => simp [put, read, h, R.wire_select w a h]

@[simp] theorem put_put (s : W → D) (v v' : A → D) :
    R.put (R.put s v) v' = R.put s v' := by
  funext w; cases h : R.select w <;> simp [put, h]

/-- Concrete extension of a local bijection, identity on its complement. -/
def lift (U : Circuit A) : Circuit W where
  run s := R.put s (U.run (R.read s))
  undo s := R.put s (U.undo (R.read s))
  undo_run s := by simp [U.undo_run]
  run_undo s := by simp [U.run_undo]

/-- CORE 2.3(c), with an arbitrary (not necessarily clean) outside frame. -/
theorem sound_lift {U : Circuit A} {κ κ' : Symbolic A X} {φ : Symbolic W X}
    (hU : Sound U κ κ') (hread : R.read φ = κ) :
    Sound (R.lift U) φ (R.put φ κ') := by
  intro x
  have hr : R.read (enc φ x) = enc κ x := by
    funext a
    exact congrFun (congrFun hread a) x
  change R.put (enc φ x) (U.run (R.read (enc φ x))) = _
  rw [hr, hU x]
  funext w
  cases hs : R.select w <;> simp [put, enc, hs]

end Region
end Pebble
