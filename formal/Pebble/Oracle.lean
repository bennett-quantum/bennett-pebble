import Pebble.Moves

/-! CORE Theorem 2.5. Interface values are arbitrary, and the compute
permutation has no access to them. Bundles may have different widths. -/
namespace Pebble

structure OracleState (W Y E : Type) where
  work : Bits W
  target : Bits Y
  fault : Bits E

variable {W Y E X : Type}

def xorBits (a b : Bits W) : Bits W := fun w => xor (a w) (b w)

theorem xorBits_cancel (a b : Bits W) : xorBits (xorBits a b) b = a := by
  funext w
  change xor (xor (a w) (b w)) (b w) = a w
  cases a w <;> cases b w <;> rfl

def onWork (U : Circuit W) : Perm (OracleState W Y E) where
  run s := { s with work := U.run s.work }
  undo s := { s with work := U.undo s.work }
  undo_run s := by cases s; simp [U.undo_run]
  run_undo s := by cases s; simp [U.run_undo]

/-- Bitwise CNOT from result bundles, preserving every work wire. -/
def commitRun (ry : Y → W) (re : E → W) (s : OracleState W Y E) :
    OracleState W Y E :=
  ⟨s.work, xorBits s.target (s.work ∘ ry), xorBits s.fault (s.work ∘ re)⟩

theorem commit_involution (ry : Y → W) (re : E → W) (s : OracleState W Y E) :
    commitRun ry re (commitRun ry re s) = s := by
  cases s
  simp [commitRun, xorBits_cancel]

def commit (ry : Y → W) (re : E → W) : Perm (OracleState W Y E) :=
  ⟨commitRun ry re, commitRun ry re, commit_involution ry re, commit_involution ry re⟩

/-- `seq` is execution order: U, K, U inverse = U⁻¹ K U. -/
def oracle (U : Circuit W) (ry : Y → W) (re : E → W) : Perm (OracleState W Y E) :=
  ((onWork U).seq (commit ry re)).seq (onWork U.inv)

/-- No hypothesis at all is imposed on κ outside the result bundles. -/
theorem oracle_contract {κ₀ κ : Symbolic W X} {U : Circuit W}
    (hU : Sound U κ₀ κ) (ry : Y → W) (re : E → W)
    (payload : X → Bits Y) (code : X → Bits E)
    (hy : ∀ x y, κ (ry y) x = payload x y)
    (he : ∀ x e, κ (re e) x = code x e)
    (x : X) (t : Bits Y) (f : Bits E) :
    (oracle U ry re).run ⟨enc κ₀ x, t, f⟩ =
      ⟨enc κ₀ x, xorBits t (payload x), xorBits f (code x)⟩ := by
  have hu := hU x
  have hy' : enc κ x ∘ ry = payload x := funext (hy x)
  have he' : enc κ x ∘ re = code x := funext (he x)
  change OracleState.mk (U.undo (U.run (enc κ₀ x)))
    (xorBits t (U.run (enc κ₀ x) ∘ ry))
    (xorBits f (U.run (enc κ₀ x) ∘ re)) = _
  rw [U.undo_run, hu, hy', he']

/-- In fact the sandwich is an involution on ALL work states, including dirty ones. -/
theorem oracle_involution (U : Circuit W) (ry : Y → W) (re : E → W)
    (s : OracleState W Y E) :
    (oracle U ry re).run ((oracle U ry re).run s) = s := by
  change (onWork U).undo ((commit ry re).run ((onWork U).run
    ((onWork U).undo ((commit ry re).run ((onWork U).run s))))) = s
  rw [(onWork U).run_undo]
  change (onWork U).undo (commitRun ry re (commitRun ry re ((onWork U).run s))) = s
  rw [commit_involution, (onWork U).undo_run]

/-- U and U inverse run unconditionally; only K carries the fresh control. -/
def controlCommitOnly (U : Circuit W) (ry : Y → W) (re : E → W) :
    Perm (Bool × OracleState W Y E) :=
  let C := Perm.onSecond (B := Bool) (onWork U)
  (C.seq (Perm.controlled (commit ry re))).seq C.inv

/-- Only commit carries the inherited fresh control. This equality is global. -/
theorem oracle_controlled (U : Circuit W) (ry : Y → W) (re : E → W)
    (q : Bool) (s : OracleState W Y E) :
    (controlCommitOnly U ry re).run (q,s) =
      (Perm.controlled (oracle U ry re)).run (q,s) := by
  cases q <;> simp [controlCommitOnly, Perm.onSecond, Perm.controlled,
    oracle, Perm.seq, onWork, Perm.inv, U.undo_run]

/-- If two computes produce the same results, their arbitrary garbage is irrelevant. -/
theorem oracle_garbage_independent {κ₀ κ₁ κ₂ : Symbolic W X} {U V : Circuit W}
    (hU : Sound U κ₀ κ₁) (hV : Sound V κ₀ κ₂)
    (ry : Y → W) (re : E → W)
    (hy : ∀ x y, κ₁ (ry y) x = κ₂ (ry y) x)
    (he : ∀ x e, κ₁ (re e) x = κ₂ (re e) x)
    (x : X) (t : Bits Y) (f : Bits E) :
    (oracle U ry re).run ⟨enc κ₀ x, t, f⟩ =
      (oracle V ry re).run ⟨enc κ₀ x, t, f⟩ := by
  rw [oracle_contract hU ry re (fun x y => κ₂ (ry y) x)
    (fun x e => κ₂ (re e) x) hy he,
    oracle_contract hV ry re (fun x y => κ₂ (ry y) x)
    (fun x e => κ₂ (re e) x) (fun _ _ => rfl) (fun _ _ => rfl)]

/-- Dirty wires may also be USED by compute. Its sound specification must hold
uniformly over every dirty assignment, and the result bits must be independent
of that assignment. No claim about arbitrary dirty use follows from a clean-only
specification. Temporary changes to dirty wires are allowed by this theorem. -/
theorem dirty_oracle_contract {B : Type} {κ₀ : Symbolic W X}
    {κ : Symbolic (Sum W B) (X × Bits B)} {U : Circuit (Sum W B)}
    (hU : Sound U (Sum.elim (fun w z => κ₀ w z.1) (fun b z => z.2 b)) κ)
    (ry : Y → Sum W B) (re : E → Sum W B)
    (payload : X → Bits Y) (code : X → Bits E)
    (hy : ∀ x dirty y, κ (ry y) (x,dirty) = payload x y)
    (he : ∀ x dirty e, κ (re e) (x,dirty) = code x e)
    (x : X) (dirty : Bits B) (t : Bits Y) (f : Bits E) :
    (oracle U ry re).run ⟨Sum.elim (enc κ₀ x) dirty, t, f⟩ =
      ⟨Sum.elim (enc κ₀ x) dirty, xorBits t (payload x), xorBits f (code x)⟩ := by
  have hh := oracle_contract hU ry re (fun z => payload z.1) (fun z => code z.1)
    (fun z y => hy z.1 z.2 y) (fun z e => he z.1 z.2 e) (x,dirty) t f
  have hs : enc (Sum.elim (fun w z => κ₀ w z.1) (fun b z => z.2 b)) (x,dirty) =
      Sum.elim (enc κ₀ x) dirty := by
    funext w; cases w <;> rfl
  simpa only [hs] using hh

/-- Borrowing arbitrary dirty wires that compute never touches. The dirty
assignment is universally quantified and restored exactly, as are the work wires. -/
theorem borrowed_oracle_contract {B : Type} {κ₀ κ : Symbolic W X} {U : Circuit W}
    (hU : Sound U κ₀ κ) (ry : Y → W) (re : E → W)
    (payload : X → Bits Y) (code : X → Bits E)
    (hy : ∀ x y, κ (ry y) x = payload x y)
    (he : ∀ x e, κ (re e) x = code x e)
    (x : X) (dirty : Bits B) (t : Bits Y) (f : Bits E) :
    (oracle (frame (B := B) U) (fun y => .inl (ry y)) (fun e => .inl (re e))).run
      ⟨Sum.elim (enc κ₀ x) dirty, t, f⟩ =
      ⟨Sum.elim (enc κ₀ x) dirty, xorBits t (payload x), xorBits f (code x)⟩ := by
  let start' : Symbolic (Sum W B) (X × Bits B) :=
    Sum.elim (fun w z => κ₀ w z.1) (fun b z => z.2 b)
  let end' : Symbolic (Sum W B) (X × Bits B) :=
    Sum.elim (fun w z => κ w z.1) (fun b z => z.2 b)
  have h : Sound (frame (B := B) U) start' end' :=
    sound_frame (fun (z : X × Bits B) => hU z.1) (fun b (z : X × Bits B) => z.2 b)
  have hh := oracle_contract h (fun y => .inl (ry y)) (fun e => .inl (re e))
    (fun z => payload z.1) (fun z => code z.1)
    (fun z y => hy z.1 y) (fun z e => he z.1 e) (x, dirty) t f
  have hs : enc start' (x,dirty) = Sum.elim (enc κ₀ x) dirty := by
    funext w; cases w <;> rfl
  simpa only [hs] using hh

/-- Explicit input/scratch partition: only the initial input bundle may be nonzero. -/
def initial (input : X → Bits I) : Symbolic (Sum I S) X :=
  Sum.elim (fun i x => input x i) (fun _ _ => false)

/-- The exact clean-scratch domain, with arbitrary targets and faults. -/
theorem clean_oracle_contract {I S : Type} {κ : Symbolic (Sum I S) X}
    (input : X → Bits I) {U : Circuit (Sum I S)}
    (hU : Sound U (initial input) κ) (ry : Y → Sum I S) (re : E → Sum I S)
    (payload : X → Bits Y) (code : X → Bits E)
    (hy : ∀ x y, κ (ry y) x = payload x y)
    (he : ∀ x e, κ (re e) x = code x e) (x : X) (t : Bits Y) (f : Bits E) :
    (oracle U ry re).run ⟨Sum.elim (input x) (fun _ => false), t, f⟩ =
      ⟨Sum.elim (input x) (fun _ => false), xorBits t (payload x), xorBits f (code x)⟩ :=
  by
    have hinit : enc (initial (S := S) input) x = Sum.elim (input x) (fun _ => false) := by
      funext w; cases w <;> rfl
    simpa only [hinit] using oracle_contract hU ry re payload code hy he x t f

end Pebble
