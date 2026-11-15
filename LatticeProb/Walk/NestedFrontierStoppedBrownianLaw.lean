import LatticeProb.Walk.NestedStoppedCurveLaw
import LatticeProb.Walk.FrontierStoppedBrownianLaw

/-! # Brownian comparison for nested stopped walk laws -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- A frontier comparison for a walk absorbed in a larger set transfers to
its curve law stopped in a nested set. -/
theorem levyProkhorov_nested_stoppedBrownian_le_of_frontier_cutoff {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (A : Set V)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V)
    (p q : V → Euc d) (U : Set (Euc d)) (z : Euc d)
    (hsub : p ⁻¹' U ⊆ A)
    (hB : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v)
    (μ : Measure (BrownianPath d)) (δ : ℝ) (r : ℝ≥0)
    (hδ : ∀ v, dist (p v) (q v) ≤ δ) (hδr : δ < (r : ℝ)) (n : ℕ)
    (hbound : (N.trajectoryLaw A hA v)
        {ω | (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω} +
      ∑ k ∈ Finset.range n, (N.trajectoryLaw A hA v) {ω | q (ω k) ∈
        Metric.thickening (r : ℝ) (frontier U)} ≤ (r : ℝ≥0∞))
    (s : ℝ≥0∞)
    (hsource : levyProkhorovEDist
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve q (q ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ s) :
    levyProkhorovEDist
      ((N.trajectoryLaw (p ⁻¹' U) hB v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ (r : ℝ≥0∞) + s := by
  rw [← trajectoryLaw_map_stoppedPolygonalCurve_of_subset N p hsub hA hB v]
  exact levyProkhorov_stoppedBrownian_le_of_frontier_cutoff
    N A hA v p q U z μ δ r hδ hδr n hbound s hsource

end LatticeProb
end
