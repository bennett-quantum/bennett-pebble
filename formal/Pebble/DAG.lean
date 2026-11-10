import Pebble.Rules

/-! CORE 3.3: a finite DAG, reversible pebbling, an XOR-evaluator
specification, and a compilation of every valid strategy. -/
namespace Pebble
namespace DAG

structure Graph (n : Nat) where
  parent : Fin n → Fin n → Prop
  acyclic : ∀ v p, parent v p → p.val < v.val
  input : Fin n → Bool
  input_no_parent : ∀ v p, input v = true → ¬ parent v p

variable {n : Nat} {X : Type} {width : Fin n → Nat}
abbrev Config (n : Nat) := Fin n → Bool
abbrev Wire (width : Fin n → Nat) := (v : Fin n) × Fin (width v)

def state (value : (v : Fin n) → X → Bits (Fin (width v)))
    (c : Config n) : Symbolic (Wire width) X :=
  fun w x => if c w.1 then value w.1 x w.2 else false

def toggle (c : Config n) (v : Fin n) : Config n :=
  fun w => if w = v then !(c w) else c w

def Enabled (G : Graph n) (c : Config n) (v : Fin n) : Prop :=
  G.input v = false ∧ ∀ p, G.parent v p → c p = true

/-- Validity checks each intermediate configuration, not just the final set. -/
inductive Valid (G : Graph n) : Config n → List (Fin n) → Config n → Prop
  | nil (c) : Valid G c [] c
  | cons {c d v vs} : Enabled G c v → Valid G (toggle c v) vs d →
      Valid G c (v :: vs) d

/-- An evaluator must XOR the denotation into arbitrary target bits while
preserving every other wire, when its predecessor bundles hold their values. -/
def EvalSpec (G : Graph n)
    (value : (v : Fin n) → X → Bits (Fin (width v)))
    (eval : Fin n → Circuit (Wire width)) : Prop :=
  ∀ v x s, (∀ p, G.parent v p → ∀ i, s ⟨p,i⟩ = value p x i) →
    ∀ w, (eval v).run s w =
      if w.1 = v then xor (s w) (value w.1 x w.2) else s w

/-- One legal add/remove pebble is a sound Eval step. -/
theorem toggle_sound (G : Graph n)
    (value : (v : Fin n) → X → Bits (Fin (width v)))
    (eval : Fin n → Circuit (Wire width)) (spec : EvalSpec G value eval)
    {c : Config n} {v : Fin n} (h : Enabled G c v) :
    Sound (eval v) (state value c) (state value (toggle c v)) := by
  intro x
  funext w
  have hs : ∀ p, G.parent v p → ∀ i,
      enc (state value c) x ⟨p,i⟩ = value p x i := by
    intro p hp i
    simp [enc, state, h.2 p hp]
  calc
    (eval v).run (enc (state value c) x) w = (if w.1 = v then xor (enc (state value c) x w) (value w.1 x w.2)
        else enc (state value c) x w) := spec v x _ hs w
    _ = enc (state value (toggle c v)) x w := by
      by_cases hw : w.1 = v
      · simp only [hw, ↓reduceIte]
        simp only [enc, state, toggle, hw, ↓reduceIte]
        cases hc : c w.1 <;> cases hv : value w.1 x w.2 <;> simp_all
      · simp [hw, enc, state, toggle]

def compile (eval : Fin n → Circuit (Wire width)) : List (Fin n) → Circuit (Wire width)
  | [] => Perm.id
  | v :: vs => (eval v).seq (compile eval vs)

/-- CORE 3.3: any valid strategy from inputs only reaches exactly its pebbled set. -/
theorem strategy_sound (G : Graph n)
    (value : (v : Fin n) → X → Bits (Fin (width v)))
    (eval : Fin n → Circuit (Wire width)) (spec : EvalSpec G value eval)
    {play : List (Fin n)} {final : Config n} (valid : Valid G G.input play final) :
    Sound (compile eval play) (state value G.input) (state value final) := by
  generalize hc : G.input = start at valid ⊢
  clear hc
  induction valid with
  | nil c => exact sound_id _
  | cons h _ ih => exact sound_comp (toggle_sound G value eval spec h) ih

/-- The same valid strategy is explicitly a derivation in the sound rule calculus. -/
theorem strategy_derivation (G : Graph n)
    (value : (v : Fin n) → X → Bits (Fin (width v)))
    (eval : Fin n → Circuit (Wire width)) (spec : EvalSpec G value eval)
    {play : List (Fin n)} {final : Config n} (valid : Valid G G.input play final) :
    Rules.Derivation (state value G.input) (state value final) (compile eval play) :=
  by
    generalize hc : G.input = start at valid ⊢
    clear hc
    induction valid with
    | nil c => exact .refl _
    | cons h _ ih => exact .seq (.primitive (toggle_sound G value eval spec h)) ih

end DAG
end Pebble
