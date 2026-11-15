import LatticeProb.Walk.StoppedCurveMembershipCutoff

/-! # Finite-window frontier estimates for stopped curve laws -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- The exit tail and finitely many frontier-visit probabilities control the
stopped curve laws for two uniformly close choices of representative. -/
theorem levyProkhorov_stoppedCurve_le_of_frontier_cutoff {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (p q : V → Euc d) (U : Set (Euc d)) (μ : Measure (ℕ → V))
    (δ : ℝ) (r : ℝ≥0) (hδ : ∀ v, dist (p v) (q v) ≤ δ)
    (hδr : δ < (r : ℝ)) (N : ℕ)
    (hbound : μ {ω | (N : WithTop ℕ) ≤
      FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω} +
      ∑ n ∈ Finset.range N, μ {ω | q (ω n) ∈
        Metric.thickening (r : ℝ) (frontier U)} ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (μ.map (stoppedPolygonalCurve q (q ⁻¹' U))) ≤ r := by
  apply levyProkhorov_stoppedCurve_le_of_membership_cutoff p q U μ δ r hδ hδr N
  have hsum :
      (∑ n ∈ Finset.range N, μ {ω | (n : WithTop ℕ) ≤
        FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω ∧
          ¬ (p (ω n) ∈ U ↔ q (ω n) ∈ U)}) ≤
        ∑ n ∈ Finset.range N, μ {ω | q (ω n) ∈
          Metric.thickening (r : ℝ) (frontier U)} := by
    apply Finset.sum_le_sum
    intro n hn
    apply measure_mono
    intro ω hω
    by_contra hfront
    exact hω.2 (mem_iff_mem_of_not_mem_thickening_frontier U hfront
      ((hδ (ω n)).trans_lt hδr))
  exact (add_le_add le_rfl hsum).trans hbound

end LatticeProb
end
