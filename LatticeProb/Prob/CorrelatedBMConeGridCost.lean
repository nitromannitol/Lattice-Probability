import LatticeProb.Prob.CorrelatedBMConeSeparatedGridDimension

/-!
# Expected cost of a separated factorial-grid cover

A uniform event probability bound gives a finite-sum cost bound using the
number of ordered grid pairs and the diameter of a grid neighborhood.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Bound the separated grid cost by the number of ordered pairs times a
uniform diameter and probability bound. -/
theorem separated_grid_cost_le_of_uniform_probability
    (μ : Measure Path2) (direction C α d : ℝ) (k n : ℕ) (β : ℝ≥0) (P : ℝ≥0∞)
    (hP : ∀ i j : Fin (n.factorial ^ 6),
      d < (j.val : ℝ) / (n.factorial ^ 6 : ℕ) -
          (i.val : ℝ) / (n.factorial ^ 6 : ℕ) →
      μ (factorialConeGridEvent direction C α k n i j) ≤ P) :
    (∑ ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
      if d < (ij.2.val : ℝ) / (n.factorial ^ 6 : ℕ) -
          (ij.1.val : ℝ) / (n.factorial ^ 6 : ℕ) then
        Metric.ediam (factorialGridNeighborhood n ij.1 ij.2) ^ (β : ℝ) *
          μ (factorialConeGridEvent direction C α k n ij.1 ij.2)
      else 0) ≤
    ((n.factorial ^ 6 : ℕ) : ℝ≥0∞) ^ 2 *
      ((ENNReal.ofReal (2 * factorialGridMesh n)) ^ (β : ℝ) * P) := by
  classical
  calc
    _ ≤ ∑ _ij : Fin (n.factorial ^ 6) × Fin (n.factorial ^ 6),
        (ENNReal.ofReal (2 * factorialGridMesh n)) ^ (β : ℝ) * P := by
      apply Finset.sum_le_sum
      intro ij _
      split_ifs with h
      · exact mul_le_mul' (ENNReal.rpow_le_rpow
          (ediam_factorialGridNeighborhood_le n ij.1 ij.2) (by positivity))
          (hP ij.1 ij.2 h)
      · exact bot_le
    _ = _ := by simp [Fintype.card_prod, pow_two, mul_assoc]

end LatticeProb.CorrelatedBM
