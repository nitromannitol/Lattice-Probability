import LatticeProb.Walk.CellConfigLocalDiameter
import LatticeProb.Walk.BoundaryExitHitTime

/-! # Local mesh bounds at the first exit edge -/

set_option autoImplicit false
noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- A local mesh bound controls the final edge before the first exterior
vertex, provided the interior has a buffer inside the mesh region. -/
theorem firstExit_finalEdge_error_lt_of_scaled_local_mesh (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (U W : Set Plane) (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ U, Metric.closedBall x (a * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), a • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (ω : ℕ → H.cells) (n : ℕ)
    (hhit : hitTime {K : H.cells | a • p K ∉ U} ω = (n + 1 : ℕ))
    (hadj : H.Adj (ω n) (ω (n + 1))) (r : ℝ≥0)
    (hr : ENNReal.ofReal (4 * (a * δ)) < (r : ℝ≥0∞)) :
    ENNReal.ofReal (2 * (a * (Metric.diam ((ω n).1 : Set Plane) +
      Metric.diam ((ω (n + 1)).1 : Set Plane)))) < (r : ℝ≥0∞) := by
  have hin : a • p (ω n) ∈ U := by
    have h := (hitTime_eq_coe_iff.mp hhit).2 n (Nat.lt_succ_self n)
    exact not_not.mp h
  have hd := diam_add_le_of_adj_of_scaled_local_bound H hH p hp U W a δ
    ha hδ hbuffer hmesh hin hadj
  have hmul : 2 * (a * (Metric.diam ((ω n).1 : Set Plane) +
      Metric.diam ((ω (n + 1)).1 : Set Plane))) ≤ 4 * (a * δ) := by
    nlinarith [mul_le_mul_of_nonneg_left hd ha]
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hmul) hr

end LatticeProb.CellConfigInterpolation
end
