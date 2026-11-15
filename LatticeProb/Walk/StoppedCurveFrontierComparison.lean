import LatticeProb.Walk.StoppedCurveRepresentativeDistance
import LatticeProb.Prob.SelectorFrontierCoupling
import LatticeProb.Bonanno.BouRabeeGwynne.ReconstructedLawComparison
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveMeasurable

/-! # Stopped curve laws for nearby representatives -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- The discrete exit time depends only on the membership of visited vertices. -/
theorem exitTime_eq_of_membership_on_path {V : Type*} (A B : Set V) (ω : ℕ → V)
    (h : ∀ n, ω n ∈ A ↔ ω n ∈ B) :
    FiniteConductanceNetwork.exitTime A ω = FiniteConductanceNetwork.exitTime B ω := by
  classical
  simp only [FiniteConductanceNetwork.exitTime, MeasureTheory.hittingAfter]
  have heq : {n : ℕ | 0 ≤ n ∧ ω n ∈ Aᶜ} = {n : ℕ | 0 ≤ n ∧ ω n ∈ Bᶜ} := by
    ext n
    simp only [mem_ofPred_eq, mem_compl_iff, h n]
  have hex : (∃ n : ℕ, 0 ≤ n ∧ ω n ∈ Aᶜ) ↔
      (∃ n : ℕ, 0 ≤ n ∧ ω n ∈ Bᶜ) := by
    simp only [mem_compl_iff, h]
  rw [heq]
  exact if_congr hex rfl rfl

/-- Changing representatives changes the stopped curve law by at most `r`
when frontier visits have mass at most `r` and all representatives are
strictly closer than `r`. -/
theorem levyProkhorov_stoppedCurve_le_of_frontier_visit {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (p q : V → Euc d) (U : Set (Euc d)) (μ : Measure (ℕ → V))
    (δ : ℝ) (r : ℝ≥0) (hδ : ∀ v, dist (p v) (q v) ≤ δ)
    (hδr : δ < (r : ℝ))
    (hbad : μ {ω | ∃ n, q (ω n) ∈ Metric.thickening (r : ℝ) (frontier U)} ≤
      (r : ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (μ.map (stoppedPolygonalCurve q (q ⁻¹' U))) ≤ r := by
  apply levyProkhorov_curveLaws_le_of_ae_good μ _ _
    (measurable_stoppedPolygonalCurve _ _).aemeasurable
    (measurable_stoppedPolygonalCurve _ _).aemeasurable _ r hbad
  filter_upwards with ω hω
  have hmem : ∀ n, ω n ∈ p ⁻¹' U ↔ ω n ∈ q ⁻¹' U := by
    intro n
    apply mem_iff_mem_of_not_mem_thickening_frontier U
    · intro hn
      exact hω ⟨n, hn⟩
    · exact (hδ (ω n)).trans_lt hδr
  have hexit := exitTime_eq_of_membership_on_path (p ⁻¹' U) (q ⁻¹' U) ω hmem
  have hc := edist_stoppedPolygonalCurve_le_of_dist_le p q (p ⁻¹' U) ω hδ
  have heq : stoppedPolygonalCurve q (p ⁻¹' U) ω =
      stoppedPolygonalCurve q (q ⁻¹' U) ω := by
    simp only [stoppedPolygonalCurve, hexit]
  rw [heq] at hc
  have hδ0 : 0 ≤ δ := dist_nonneg.trans (hδ (ω 0))
  exact hc.trans_lt (by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ0).2 hδr)

end LatticeProb
end
