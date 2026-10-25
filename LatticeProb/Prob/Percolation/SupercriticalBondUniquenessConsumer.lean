import LatticeProb.External.SupercriticalBondUniquenessInput

/-!
# A parameter in the strictly supercritical interval

The explicit classical cited input gives a parameter strictly between the canonical
critical probability and one in every source dimension.
-/

namespace LatticeProb.External

open LatticeProb.Percolation

/-- The cited upper critical bound supplies a genuine parameter in the source interval. -/
theorem exists_supercritical_parameter_of_classical_input
    (hclassical : SupercriticalBondUniqueness) (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p : unitInterval, criticalProbability d < (p : ℝ) ∧ (p : ℝ) < 1 := by
  obtain ⟨q, hq0, hq1⟩ := exists_between (hclassical.1 d hd).2
  exact ⟨⟨q, (criticalProbability_nonneg d).trans hq0.le, hq1.le⟩, hq0, hq1⟩

end LatticeProb.External
