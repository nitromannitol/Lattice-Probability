/- # Couplings of finite random sets from increasing-event domination

Specialize the finite partial-order coupling to inclusion of finite subsets; insertion closure gives the required upper-set condition.
-/

import LatticeProb.Prob.Strassen.FiniteOrder



open scoped BigOperators

namespace LatticeProb.StrassenAux

/-- **Finite subset-supported coupling.** Domination on insertion-closed families produces the complete subset-supported
atom coupling of the original probability weights. -/
theorem exists_subset_matrix_of_event_domination
    {E : Type*} [Fintype E] [DecidableEq E]
    (p₁ p₂ : Finset E → ℝ) (hp₁ : ∀ S, 0 ≤ p₁ S) (hp₂ : ∀ S, 0 ≤ p₂ S)
    (hsum₁ : ∑ S, p₁ S = 1) (hsum₂ : ∑ S, p₂ S = 1)
    (hdom : ∀ ev : Set (Finset E), (∀ S ∈ ev, ∀ e : E, insert e S ∈ ev) →
      ∑ S, Set.indicator ev p₁ S ≤ ∑ S, Set.indicator ev p₂ S) :
    ∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = p₁ S) ∧
      (∀ T, ∑ S, q S T = p₂ T) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, ¬ S ⊆ T → q S T = 0) := by
  apply exists_monotone_matrix_of_upper_set_domination p₁ p₂ hp₁ hp₂ hsum₁ hsum₂
  intro ev hev
  apply hdom ev
  intro S hS e
  exact hev (Finset.subset_insert e S) hS

end LatticeProb.StrassenAux
