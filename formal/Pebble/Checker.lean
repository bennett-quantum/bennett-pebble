import Pebble.Chain

/-! A verified, executable checker for allocated chain plays. It rejects illegal
moves or any capacity violation, and reports exact live-value peak and game cost.
This is an expanded-list checker, not a compressed-schedule algorithm. -/
namespace Pebble
namespace Chain

variable {T P : Nat}

structure Report (T P : Nat) where
  final : Config T P
  peak : Nat
  cost : Nat

/-- Independent, unchecked replay and structural accounting specifications. -/
def replay (c : Config T P) : List (Move T P) → Config T P
  | [] => c
  | a :: as => replay (applyMove c a) as

def peakSpace (m r : Nat) (c : Config T P) : List (Move T P) → Nat
  | [] => space m r c
  | a :: as => max (space m r c) (peakSpace m r (applyMove c a) as)

def totalCost (a k : Nat) : List (Move T P) → Nat
  | [] => 0
  | mv :: as => moveCost a k mv + totalCost a k as

/-- `none` is rejection. Both the start and every intermediate/final state
are checked against S. Finite indices exclude out-of-range moves by construction. -/
def checkFrom (m r S a k : Nat) (c : Config T P) :
    List (Move T P) → Option (Report T P)
  | [] => if space m r c ≤ S then some ⟨c, space m r c, 0⟩ else none
  | mv :: as =>
    if space m r c ≤ S ∧ Enabled c mv then
      match checkFrom m r S a k (applyMove c mv) as with
      | none => none
      | some q => some ⟨q.final, max (space m r c) q.peak, moveCost a k mv + q.cost⟩
    else none

/-- Priority 6: acceptance implies legality, correct endpoint, exact peak and cost. -/
theorem checker_sound {m r S a k : Nat} {c : Config T P}
    {play : List (Move T P)} {q : Report T P}
    (accepted : checkFrom m r S a k c play = some q) :
    Legal m r S c play q.final ∧ q.final = replay c play ∧
      q.peak = peakSpace m r c play ∧ q.cost = totalCost a k play := by
  induction play generalizing c q with
  | nil =>
    simp only [checkFrom] at accepted
    split at accepted
    · cases accepted
      exact ⟨.nil ‹_›, rfl, rfl, rfl⟩
    · contradiction
  | cons mv as ih =>
    simp only [checkFrom] at accepted
    split at accepted
    · rename_i h
      cases hrec : checkFrom m r S a k (applyMove c mv) as with
      | none => simp [hrec] at accepted
      | some tail =>
        simp only [hrec] at accepted
        cases accepted
        obtain ⟨hl, hf, hp, hc⟩ := ih hrec
        exact ⟨.cons h.1 h.2 hl, hf, congrArg (max (space m r c)) hp,
          congrArg (fun n => moveCost a k mv + n) hc⟩
    · contradiction

/-- Completeness: legality is exactly what the checker accepts. -/
theorem checker_complete {m r S a k : Nat} {c d : Config T P}
    {play : List (Move T P)} (legal : Legal m r S c play d) :
    ∃ q, checkFrom m r S a k c play = some q ∧ q.final = d := by
  induction legal with
  | @nil c h => exact ⟨⟨c, space m r c, 0⟩, by simp [checkFrom, h], rfl⟩
  | @cons c d mv as h he _ ih =>
    obtain ⟨tail, ht, hf⟩ := ih
    exact ⟨⟨tail.final, max (space m r c) tail.peak, moveCost a k mv + tail.cost⟩,
      by simp [checkFrom, h, he, ht], hf⟩

def accepts (m r S a k : Nat) (slot : Fin P) (play : List (Move T P)) : Bool :=
  (checkFrom m r S a k (start slot) play).isSome

theorem accepts_iff_legal (m r S a k : Nat) (slot : Fin P) (play : List (Move T P)) :
    accepts m r S a k slot play = true ↔ ∃ d, Legal m r S (start slot) play d := by
  constructor
  · intro h
    unfold accepts at h
    cases hc : checkFrom m r S a k (start slot) play with
    | none => simp [hc] at h
    | some q => exact ⟨q.final, (checker_sound hc).1⟩
  · rintro ⟨d, hl⟩
    obtain ⟨q, hq, _⟩ := checker_complete (a := a) (k := k) hl
    simp [accepts, hq]

theorem legal_peak_bound {m r S : Nat} {c d : Config T P}
    {play : List (Move T P)} (h : Legal m r S c play d) :
    peakSpace m r c play ≤ S := by
  induction h with
  | nil h => exact h
  | cons h _ _ ih => exact Nat.max_le.mpr ⟨h, ih⟩

theorem checker_peak_bound {m r S a k : Nat} {c : Config T P}
    {play : List (Move T P)} {q : Report T P}
    (accepted : checkFrom m r S a k c play = some q) : q.peak ≤ S := by
  rw [(checker_sound accepted).2.2.1]
  exact legal_peak_bound (checker_sound accepted).1

/-- The executable checker, local step certificates and final result reads suffice
for oracle correctness; the schedule producer supplies no proof. -/
theorem checked_play_oracle {m r S a k : Nat} {X Y E : Type}
    (σ : Fin (T+1) → X → Bits (Fin m)) (ρ : Fin T → X → Bits (Fin r))
    (step : Fin T → Circuit (Sum (Fin m) (Fin r))) (spec : StepSound σ ρ step)
    (initialSlot resultSlot : Fin P) {play : List (Move T P)} {q : Report T P}
    (accepted : checkFrom m r S a k (start initialSlot) play = some q)
    (goal : q.final.token resultSlot = some ⟨T, Nat.lt_succ_self T⟩)
    (yi : Y → Fin m) (ei : E → Fin m) (payload : X → Bits Y) (code : X → Bits E)
    (hy : ∀ x y, σ ⟨T, Nat.lt_succ_self T⟩ x (yi y) = payload x y)
    (he : ∀ x e, σ ⟨T, Nat.lt_succ_self T⟩ x (ei e) = code x e)
    (x : X) (t : Bits Y) (f : Bits E) :
    (oracle (compile step play) (fun y => .inl (resultSlot, yi y))
      (fun e => .inl (resultSlot, ei e))).run
      ⟨enc (state σ ρ (start initialSlot)) x, t, f⟩ =
      ⟨enc (state σ ρ (start initialSlot)) x, xorBits t (payload x), xorBits f (code x)⟩ :=
  legal_play_oracle σ ρ step spec initialSlot resultSlot
    (checker_sound accepted).1 goal yi ei payload code hy he x t f

end Chain
end Pebble
