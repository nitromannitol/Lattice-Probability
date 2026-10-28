import LatticeProb.Prob.Percolation.AntalPisztoraEvent
import LatticeProb.Prob.Percolation.LatticeBondCritical

/-!
# Antal–Pisztora finite-box input

This proposition records an unproved cited input: the exponential estimate for
an explicit projection of the finite-box event.  Its definition proves no
probability estimate and introduces no axiom.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.External

open LatticeProb.Percolation

/-- The projected Antal–Pisztora finite-box bound, with constants uniform in scale
and integer translation.  This proposition is an unproved cited input. -/
def AntalPisztoraProjectedBox : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ (N : {n : ℕ // 0 < n}), N₀ ≤ N.val → 10 < N.val → N.val % 8 = 0 →
        ∀ a : Vertex d,
          latticeBondLaw d p (apProjectedEvent a N)ᶜ ≤
            ENNReal.ofReal (C * Real.exp (-c * (N.val : ℝ)))

end LatticeProb.External
