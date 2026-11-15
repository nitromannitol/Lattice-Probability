import LatticeProb.Walk.StoppedCurveFrontierCutoff

/-! # Stopped Brownian comparison under a change of vertex positions -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- A stopped Brownian comparison transfers to nearby vertex positions when
frontier visits and the reference exit tail have the stated bounds. -/
theorem levyProkhorov_stoppedBrownian_le_of_frontier_cutoff {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (A : Set V)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V)
    (p q : V → Euc d) (U : Set (Euc d)) (z : Euc d)
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
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ (r : ℝ≥0∞) + s := by
  exact (levyProkhorovEDist_triangle _ _ _).trans
    (add_le_add (levyProkhorov_stoppedCurve_le_of_frontier_cutoff
      p q U (N.trajectoryLaw A hA v) δ r hδ hδr n hbound) hsource)

end LatticeProb
end
