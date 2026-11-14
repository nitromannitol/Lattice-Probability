import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Paths driven by a sequence of updates

A jointly measurable update yields a jointly measurable path in its initial
state and noise sequence. Each position depends only on the earlier noise.
-/

set_option autoImplicit false

namespace LatticeProb

variable {X U : Type*}

/-- The path obtained by iterating an update with successive instructions. -/
def drivenPath (F : X → U → X) (x : X) (u : ℕ → U) : ℕ → X
  | 0 => x
  | n + 1 => F (drivenPath F x u n) (u n)

@[simp] theorem drivenPath_zero (F : X → U → X) (x : X) (u : ℕ → U) :
    drivenPath F x u 0 = x := rfl

@[simp] theorem drivenPath_succ (F : X → U → X) (x : X) (u : ℕ → U) (n : ℕ) :
    drivenPath F x u (n + 1) = F (drivenPath F x u n) (u n) := rfl

/-- The position at time `n` depends only on the first `n` instructions. -/
theorem drivenPath_eq_of_prefix_eq (F : X → U → X) (x : X) (u v : ℕ → U)
    (n : ℕ) (h : ∀ j < n, u j = v j) : drivenPath F x u n = drivenPath F x v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [drivenPath_succ, drivenPath_succ, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)),
      h n (Nat.lt_succ_self n)]

variable [MeasurableSpace X] [MeasurableSpace U]

/-- All positions are jointly measurable in the initial state and instruction sequence. -/
theorem measurable_drivenPath (F : X → U → X) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun p : X × (ℕ → U) => drivenPath F p.1 p.2) := by
  apply Measurable.of_eval
  intro n
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact hF.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd))

end LatticeProb
