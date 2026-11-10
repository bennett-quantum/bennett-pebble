import Pebble.DAG

/-! CORE §6. Tokens occupy explicit disjoint physical slots; forgetting slots
recovers token multiplicities. Retained residues have one bundle per time index.
Every local step is lifted by the proved frame rule, never by a scheduler axiom. -/
namespace Pebble
namespace Chain

variable {T P m r : Nat} {X : Type}

structure Config (T P : Nat) where
  token : Fin P → Option (Fin (T+1))
  residue : Fin T → Bool

abbrev Wire (T P m r : Nat) := Sum (Fin P × Fin m) (Fin T × Fin r)

inductive Move (T P : Nat) where
  | adv (slot : Fin P) (j : Fin T)
  | ret (slot : Fin P) (j : Fin T)
  | dup (src dst : Fin P) (j : Fin (T+1))
  | undup (src dst : Fin P) (j : Fin (T+1))
  deriving Repr, DecidableEq

def setToken (c : Config T P) (s : Fin P) (pos : Option (Fin (T+1))) : Config T P :=
  { c with token := fun t => if t = s then pos else c.token t }

def setStep (c : Config T P) (s : Fin P) (pos : Fin (T+1))
    (j : Fin T) (live : Bool) : Config T P :=
  { token := (setToken c s (some pos)).token
    residue := fun i => if i = j then live else c.residue i }

def applyMove (c : Config T P) : Move T P → Config T P
  | .adv s j => setStep c s j.succ j true
  | .ret s j => setStep c s j.castSucc j false
  | .dup _ dst j => setToken c dst (some j)
  | .undup _ dst _ => setToken c dst none

def Enabled (c : Config T P) : Move T P → Prop
  | .adv s j => c.token s = some j.castSucc ∧ c.residue j = false
  | .ret s j => c.token s = some j.succ ∧ c.residue j = true
  | .dup src dst j => src ≠ dst ∧ c.token src = some j ∧ c.token dst = none
  | .undup src dst j => src ≠ dst ∧ c.token src = some j ∧ c.token dst = some j

instance (c : Config T P) (a : Move T P) : Decidable (Enabled c a) := by
  cases a <;> unfold Enabled <;> infer_instance

/-- The CORE live-value space convention; clean/free slots contribute zero. -/
def space (m r : Nat) (c : Config T P) : Nat :=
  m * ((List.finRange P).filter (fun s => (c.token s).isSome)).length +
  r * ((List.finRange T).filter (fun j => c.residue j)).length

def moveCost (a k : Nat) : Move T P → Nat
  | .adv .. | .ret .. => a
  | .dup .. | .undup .. => k

inductive Legal (m r S : Nat) : Config T P → List (Move T P) → Config T P → Prop
  | nil {c} : space m r c ≤ S → Legal m r S c [] c
  | cons {c d a as} : space m r c ≤ S → Enabled c a →
      Legal m r S (applyMove c a) as d → Legal m r S c (a :: as) d

/-- One distinguished initial slot; its σ₀ may be an arbitrary input function. -/
def start (slot : Fin P) : Config T P :=
  ⟨fun s => if s = slot then some ⟨0, Nat.zero_lt_succ T⟩ else none, fun _ => false⟩

def Goal (c : Config T P) : Prop := ∃ s, c.token s = some ⟨T, Nat.lt_succ_self T⟩

def state (σ : Fin (T+1) → X → Bits (Fin m)) (ρ : Fin T → X → Bits (Fin r))
    (c : Config T P) : Symbolic (Wire T P m r) X :=
  Sum.elim
    (fun w x => match c.token w.1 with | some j => σ j x w.2 | none => false)
    (fun w x => if c.residue w.1 then ρ w.1 x w.2 else false)

/-- The local σ-slot plus residue bundle of a time step. -/
def stepRegion (s : Fin P) (j : Fin T) : Region (Sum (Fin m) (Fin r)) (Wire T P m r) where
  wire := Sum.elim (fun i => .inl (s,i)) (fun i => .inr (j,i))
  select := Sum.elim
    (fun w => if w.1 = s then some (.inl w.2) else none)
    (fun w => if w.1 = j then some (.inr w.2) else none)
  select_wire a := by cases a <;> simp
  wire_select w a h := by
    cases w with
    | inl w =>
      rcases w with ⟨t, i⟩
      dsimp at h ⊢
      split at h
      · simp only [Option.some.injEq] at h
        subst a
        simp_all
      · contradiction
    | inr w =>
      rcases w with ⟨t, i⟩
      dsimp at h ⊢
      split at h
      · simp only [Option.some.injEq] at h
        subst a
        simp_all
      · contradiction

/-- The source and destination of a CNOT copy. Distinct slots are mandatory. -/
def copyRegion (src dst : Fin P) (hne : src ≠ dst) :
    Region (Sum (Fin m) (Fin m)) (Wire T P m r) where
  wire := Sum.elim (fun i => .inl (src,i)) (fun i => .inl (dst,i))
  select := Sum.elim
    (fun w => if w.1 = src then some (.inl w.2)
      else if w.1 = dst then some (.inr w.2) else none)
    (fun _ => none)
  select_wire a := by
    cases a <;> simp [Ne.symm hne]
  wire_select w a h := by
    cases w with
    | inl w =>
      rcases w with ⟨t, i⟩
      dsimp at h ⊢
      split at h
      · simp only [Option.some.injEq] at h
        subst a
        simp_all
      · split at h
        · simp only [Option.some.injEq] at h
          subst a
          simp_all
        · contradiction
    | inr w => contradiction

/-- Updating a configuration agrees with writing exactly the local step outputs. -/
theorem state_setStep (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (c : Config T P) (s : Fin P)
    (pos : Fin (T+1)) (j : Fin T) (live : Bool) :
    state σ ρ (setStep c s pos j live) =
      (stepRegion s j).put (state σ ρ c)
        (Sum.elim (fun i x => σ pos x i) (fun i x => if live then ρ j x i else false)) := by
  funext w x
  cases w with
  | inl w =>
    by_cases h : w.1 = s <;> simp [state, setStep, setToken, Region.put, stepRegion, h]
  | inr w =>
    by_cases h : w.1 = j <;> simp [state, setStep, Region.put, stepRegion, h]

def before (σ : Fin (T+1) → X → Bits (Fin m)) (j : Fin T) :
    Symbolic (Sum (Fin m) (Fin r)) X :=
  Sum.elim (fun i x => σ j.castSucc x i) (fun _ _ => false)
def after (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (j : Fin T) :
    Symbolic (Sum (Fin m) (Fin r)) X :=
  Sum.elim (fun i x => σ j.succ x i) (fun i x => ρ j x i)

/-- The only chain-step hypothesis: one LOCAL sound evaluator per time index. -/
def StepSound (σ : Fin (T+1) → X → Bits (Fin m)) (ρ : Fin T → X → Bits (Fin r))
    (step : Fin T → Circuit (Sum (Fin m) (Fin r))) : Prop :=
  ∀ j, Sound (step j) (before σ j) (after σ ρ j)

def moveCircuit (step : Fin T → Circuit (Sum (Fin m) (Fin r))) :
    Move T P → Circuit (Wire T P m r)
  | .adv s j => (stepRegion s j).lift (step j)
  | .ret s j => (stepRegion s j).lift (step j).inv
  | .dup src dst _ => if h : src ≠ dst then (copyRegion src dst h).lift Rules.copy else Perm.id
  | .undup src dst _ => if h : src ≠ dst then (copyRegion src dst h).lift Rules.copy.inv else Perm.id

/-- Adv is the sound local step extended by the arbitrary remaining frame. -/
theorem adv_sound (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (step : Fin T → Circuit (Sum (Fin m) (Fin r)))
    (spec : StepSound σ ρ step) {c : Config T P} {s : Fin P} {j : Fin T}
    (h : Enabled c (.adv s j)) :
    Sound (moveCircuit step (.adv s j)) (state σ ρ c) (state σ ρ (applyMove c (.adv s j))) := by
  change Sound ((stepRegion s j).lift (step j)) _ (state σ ρ (setStep c s j.succ j true))
  rw [state_setStep]
  apply Region.sound_lift (hU := spec j)
  funext a x
  cases a <;> simp [Region.read, stepRegion, state, before, h.1, h.2]

/-- Ret uses the EXPLICIT INVERSE of the same step, including its residue. -/
theorem ret_sound (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (step : Fin T → Circuit (Sum (Fin m) (Fin r)))
    (spec : StepSound σ ρ step) {c : Config T P} {s : Fin P} {j : Fin T}
    (h : Enabled c (.ret s j)) :
    Sound (moveCircuit step (.ret s j)) (state σ ρ c) (state σ ρ (applyMove c (.ret s j))) := by
  change Sound ((stepRegion s j).lift (step j).inv) _ (state σ ρ (setStep c s j.castSucc j false))
  rw [state_setStep]
  apply Region.sound_lift (hU := sound_inverse (spec j))
  funext a x
  cases a <;> simp [Region.read, stepRegion, state, after, h.1, h.2]

/-- The copy source is framed; the destination becomes a value or clean zero. -/
theorem state_copy_update (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (c : Config T P)
    (src dst : Fin P) (j : Fin (T+1)) (live : Bool)
    (hne : src ≠ dst) (hsrc : c.token src = some j) :
    state σ ρ (setToken c dst (if live then some j else none)) =
      (copyRegion src dst hne).put (state σ ρ c)
        (Sum.elim (fun i x => σ j x i) (fun i x => if live then σ j x i else false)) := by
  funext w x
  cases w with
  | inl w =>
    by_cases hs : w.1 = src
    · simp [state, setToken, Region.put, copyRegion, hs, hne, hsrc]
    · by_cases hd : w.1 = dst <;>
        cases live <;> simp [state, setToken, Region.put, copyRegion, hs, hd, Ne.symm hne]
  | inr w => rfl

theorem dup_sound (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (step : Fin T → Circuit (Sum (Fin m) (Fin r)))
    {c : Config T P} {src dst : Fin P} {j : Fin (T+1)}
    (h : Enabled c (.dup src dst j)) :
    Sound (moveCircuit step (.dup src dst j)) (state σ ρ c)
      (state σ ρ (applyMove c (.dup src dst j))) := by
  simp only [moveCircuit, dite_eq_left h.1, applyMove]
  rw [show setToken c dst (some j) = setToken c dst (if true then some j else none) from rfl,
    state_copy_update σ ρ c src dst j true h.1 h.2.1]
  apply Region.sound_lift (hU := Rules.eval_local Rules.copy_spec (σ j) (σ j) (fun _ => rfl))
  funext a x
  cases a <;> simp [Region.read, copyRegion, state, Rules.evalBefore,
    h.2.1, h.2.2]

theorem undup_sound (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (step : Fin T → Circuit (Sum (Fin m) (Fin r)))
    {c : Config T P} {src dst : Fin P} {j : Fin (T+1)}
    (h : Enabled c (.undup src dst j)) :
    Sound (moveCircuit step (.undup src dst j)) (state σ ρ c)
      (state σ ρ (applyMove c (.undup src dst j))) := by
  simp only [moveCircuit, dite_eq_left h.1, applyMove]
  rw [show setToken c dst none = setToken c dst (if false then some j else none) from rfl,
    state_copy_update σ ρ c src dst j false h.1 h.2.1]
  apply Region.sound_lift (hU := sound_inverse
    (Rules.eval_local Rules.copy_spec (σ j) (σ j) (fun _ => rfl)))
  funext a x
  cases a <;> simp [Region.read, copyRegion, state, Rules.evalAfter,
    h.2.1, h.2.2]

theorem move_sound (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (step : Fin T → Circuit (Sum (Fin m) (Fin r)))
    (spec : StepSound σ ρ step) {c : Config T P} {a : Move T P} (h : Enabled c a) :
    Sound (moveCircuit step a) (state σ ρ c) (state σ ρ (applyMove c a)) := by
  cases a with
  | adv s j => exact adv_sound σ ρ step spec h
  | ret s j => exact ret_sound σ ρ step spec h
  | dup src dst j => exact dup_sound σ ρ step h
  | undup src dst j => exact undup_sound σ ρ step h

def compile (step : Fin T → Circuit (Sum (Fin m) (Fin r))) :
    List (Move T P) → Circuit (Wire T P m r)
  | [] => Perm.id
  | a :: as => (moveCircuit step a).seq (compile step as)

/-- CORE 6.2: EVERY legal allocated play, with arbitrary repetitions, is sound. -/
theorem legal_play_sound (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (step : Fin T → Circuit (Sum (Fin m) (Fin r)))
    (spec : StepSound σ ρ step) {c d : Config T P} {play : List (Move T P)}
    (legal : Legal m r S c play d) :
    Sound (compile step play) (state σ ρ c) (state σ ρ d) := by
  induction legal with
  | nil _ => exact sound_id _
  | cons _ enabled _ ih => exact sound_comp (move_sound σ ρ step spec enabled) ih

theorem legal_play_derivation (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (step : Fin T → Circuit (Sum (Fin m) (Fin r)))
    (spec : StepSound σ ρ step) {c d : Config T P} {play : List (Move T P)}
    (legal : Legal m r S c play d) :
    Rules.Derivation (state σ ρ c) (state σ ρ d) (compile step play) :=
  by
    induction legal with
    | nil _ => exact .refl _
    | cons _ enabled _ ih => exact .seq (.primitive (move_sound σ ρ step spec enabled)) ih

/-- In the start configuration every wire outside the single σ₀ bundle is clean. -/
theorem start_clean (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (slot : Fin P) :
    (∀ s i, s ≠ slot → Clean (state σ ρ (start slot)) (.inl (s,i))) ∧
    (∀ j i, Clean (state σ ρ (start slot)) (.inr (j,i))) := by
  constructor
  · intro s i h x; simp [state, start, h]
  · intro j i x; rfl

/-- End to end: any legal play reaching T yields the oracle contract, independently
of every other token and residue. The only function-correctness premise says that
σ_T's selected bits are payload(F_B(x)) and code(F_B(x)). -/
theorem legal_play_oracle (σ : Fin (T+1) → X → Bits (Fin m))
    (ρ : Fin T → X → Bits (Fin r)) (step : Fin T → Circuit (Sum (Fin m) (Fin r)))
    (spec : StepSound σ ρ step) (initialSlot resultSlot : Fin P)
    {d : Config T P} {play : List (Move T P)}
    (legal : Legal m r S (start initialSlot) play d)
    (goal : d.token resultSlot = some ⟨T, Nat.lt_succ_self T⟩)
    (yi : Y → Fin m) (ei : E → Fin m) (payload : X → Bits Y) (code : X → Bits E)
    (hy : ∀ x y, σ ⟨T, Nat.lt_succ_self T⟩ x (yi y) = payload x y)
    (he : ∀ x e, σ ⟨T, Nat.lt_succ_self T⟩ x (ei e) = code x e)
    (x : X) (t : Bits Y) (f : Bits E) :
    (oracle (compile step play) (fun y => .inl (resultSlot, yi y))
      (fun e => .inl (resultSlot, ei e))).run
      ⟨enc (state σ ρ (start initialSlot)) x, t, f⟩ =
      ⟨enc (state σ ρ (start initialSlot)) x, xorBits t (payload x), xorBits f (code x)⟩ := by
  apply oracle_contract (legal_play_sound σ ρ step spec legal)
  · intro x y; simpa only [state, Sum.elim_inl, goal] using hy x y
  · intro x e; simpa only [state, Sum.elim_inl, goal] using he x e

end Chain
end Pebble
