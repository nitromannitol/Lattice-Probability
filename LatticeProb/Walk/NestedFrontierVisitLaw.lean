import LatticeProb.Walk.NestedStoppedCurveLaw
import LatticeProb.Walk.StoppedCurveMembershipComparison

/-! # Nested stopped curve laws and frontier visits -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- The probability of visiting the frontier neighborhood up to and including
    the reference exit controls the change of representative. -/
theorem levyProkhorov_stoppedCurve_le_of_frontier_visit_before_exit {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (p q : V → Euc d) (U : Set (Euc d)) (μ : Measure (ℕ → V))
    (δ : ℝ) (r : ℝ≥0) (hδ : ∀ v, dist (p v) (q v) ≤ δ)
    (hδr : δ < (r : ℝ))
    (hbad : μ {ω | ∃ n : ℕ, (n : WithTop ℕ) ≤
      FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω ∧
        q (ω n) ∈ Metric.thickening (r : ℝ) (frontier U)} ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (μ.map (stoppedPolygonalCurve q (q ⁻¹' U))) ≤ r := by
  apply levyProkhorov_stoppedCurve_le_of_membership_disagreement p q U μ δ r hδ hδr
  refine (measure_mono ?_).trans hbad
  intro ω hω
  obtain ⟨n, hn, hdiff⟩ := hω
  refine ⟨n, hn, ?_⟩
  by_contra hfront
  exact hdiff (mem_iff_mem_of_not_mem_thickening_frontier U hfront
    ((hδ (ω n)).trans_lt hδr))

/-- A source comparison under the larger active law transfers to a nested
    stopped law, with the frontier visit probability kept as a single event. -/
theorem levyProkhorov_nested_stoppedBrownian_le_of_frontier_visit {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (A : Set V)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V)
    (p q : V → Euc d) (U : Set (Euc d)) (z : Euc d)
    (hsub : p ⁻¹' U ⊆ A)
    (hB : ∀ v ∈ p ⁻¹' U, 0 < N.totalConductance v)
    (μ : Measure (BrownianPath d)) (δ : ℝ) (r : ℝ≥0)
    (hδ : ∀ v, dist (p v) (q v) ≤ δ) (hδr : δ < (r : ℝ))
    (hbad : (N.trajectoryLaw A hA v) {ω | ∃ n : ℕ, (n : WithTop ℕ) ≤
      FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω ∧
        q (ω n) ∈ Metric.thickening (r : ℝ) (frontier U)} ≤ (r : ℝ≥0∞))
    (s : ℝ≥0∞)
    (hsource : levyProkhorovEDist
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve q (q ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ s) :
    levyProkhorovEDist
      ((N.trajectoryLaw (p ⁻¹' U) hB v).map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (stoppedBrownianLaw U z μ) ≤ (r : ℝ≥0∞) + s := by
  rw [← trajectoryLaw_map_stoppedPolygonalCurve_of_subset N p hsub hA hB v]
  exact (levyProkhorovEDist_triangle _ _ _).trans
    (add_le_add (levyProkhorov_stoppedCurve_le_of_frontier_visit_before_exit
      p q U (N.trajectoryLaw A hA v) δ r hδ hδr hbad) hsource)

end LatticeProb
end
