import LatticeProb.Walk.StoppedCurveFrontierComparison

/-! # Stopped curve laws under membership agreement -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- Agreement through the exit vertex of the second set determines both exit times. -/
theorem exitTime_eq_of_membership_before_exit {V : Type*} (A B : Set V) (ω : ℕ → V)
    (h : ∀ n : ℕ, (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime B ω →
      (ω n ∈ A ↔ ω n ∈ B)) :
    FiniteConductanceNetwork.exitTime A ω = FiniteConductanceNetwork.exitTime B ω := by
  classical
  apply le_antisymm
  · by_contra hn
    have hlt := lt_of_not_ge hn
    have htop : FiniteConductanceNetwork.exitTime B ω ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨n, he⟩ := WithTop.ne_top_iff_exists.mp htop
    have hout : ω n ∉ B := by
      have hh := FiniteConductanceNetwork.exitTime_mem_compl_of_ne_top htop
      simpa [← he] using hh
    rw [← he] at hlt
    have hin : ω n ∈ A := FiniteConductanceNetwork.mem_of_lt_exitTime hlt
    exact hout ((h n (le_of_eq he)).mp hin)
  · by_contra hn
    have hlt := lt_of_not_ge hn
    have htop : FiniteConductanceNetwork.exitTime A ω ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨n, he⟩ := WithTop.ne_top_iff_exists.mp htop
    have hout : ω n ∉ A := by
      have hh := FiniteConductanceNetwork.exitTime_mem_compl_of_ne_top htop
      simpa [← he] using hh
    rw [← he] at hlt
    have hin : ω n ∈ B := FiniteConductanceNetwork.mem_of_lt_exitTime hlt
    exact hout ((h n hlt.le).mpr hin)

/-- The law comparison only charges paths whose membership differs before or at
    the exit of the second representative. -/
theorem levyProkhorov_stoppedCurve_le_of_membership_disagreement {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (p q : V → Euc d) (U : Set (Euc d)) (μ : Measure (ℕ → V))
    (δ : ℝ) (r : ℝ≥0) (hδ : ∀ v, dist (p v) (q v) ≤ δ)
    (hδr : δ < (r : ℝ))
    (hbad : μ {ω | ∃ n : ℕ, (n : WithTop ℕ) ≤
      FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω ∧
      ¬ (p (ω n) ∈ U ↔ q (ω n) ∈ U)} ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (μ.map (stoppedPolygonalCurve q (q ⁻¹' U))) ≤ r := by
  apply levyProkhorov_curveLaws_le_of_ae_good μ _ _
    (measurable_stoppedPolygonalCurve _ _).aemeasurable
    (measurable_stoppedPolygonalCurve _ _).aemeasurable _ r hbad
  filter_upwards with ω hω
  have hmem : ∀ n : ℕ, (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω →
      (ω n ∈ p ⁻¹' U ↔ ω n ∈ q ⁻¹' U) := by
    intro n hn
    by_contra hh
    exact hω ⟨n, hn, hh⟩
  have hexit := exitTime_eq_of_membership_before_exit (p ⁻¹' U) (q ⁻¹' U) ω hmem
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
