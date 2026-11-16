import LatticeProb.LQG.CompactBallUniformLimitPower
import LatticeProb.LQG.LogSingularArea
import LatticeProb.LQG.WeylOffOrigin

/-! # Compact-center ball bounds for logarithmic weights -/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open MatedCRTHarmonic LQGMetric
open MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open LatticeProb.LQG.WeylOffOriginDerived

namespace LatticeProb.LQG

/-- The logarithmically weighted measure inherits the compact-center ball exponent
of the unweighted LQG measure on compact sets away from the origin. -/
theorem ae_forall_compact_center_ball_power_bound_coneMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (μ : Ω → Measure ℂ)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P,
      (∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ,
        0 < r → r ≤ 1 → μ ω (Metric.ball z r) ≤ C * ENNReal.ofReal (r ^ κ)) ∧
      ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ,
        0 < r → r ≤ 1 → r ≤ δ →
          coneMeasure γ (μ ω) (fun _ => 0) (GMSCase.logSing γ) (Metric.ball z r) ≤
            C * ENNReal.ofReal (r ^ κ) := by
  obtain ⟨κ, hκ, hb⟩ :=
    ae_forall_compact_center_ball_power_bound_of_isLQGAreaOf hH hHm hγ hγ2 hp hpq hq μ hμ
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hb] with ω hb
  refine ⟨hb, ?_⟩
  intro K hK hK0
  have hsub : K ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact hK0 hz
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_cthickening_subset_open isOpen_compl_singleton hsub
  let T : Set ℂ := Metric.cthickening δ K
  have hT : IsCompact T := hK.cthickening
  have hTc : ContinuousOn (weylFactor γ γ) T := by
    intro z hz
    apply (weylFactor_continuousAt ?_).continuousWithinAt
    have := hδsub hz
    simpa using this
  obtain ⟨M, hM⟩ := hT.bddAbove_image hTc
  obtain ⟨C, hC, hb⟩ := hb K hK
  refine ⟨δ, hδ, ENNReal.ofReal M * C, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC, ?_⟩
  intro z hz r hr hr1 hrδ
  have hball : Metric.ball z r ⊆ T := by
    intro w hw
    apply Metric.mem_cthickening_of_dist_le w z δ K hz
    exact (Metric.mem_ball.mp hw).le.trans hrδ
  have hbound : ∀ w ∈ Metric.ball z r, weylFactor γ γ w ≤ M := by
    intro w hw
    exact hM ⟨w, hball hw, rfl⟩
  calc coneMeasure γ (μ ω) (fun _ => 0) (GMSCase.logSing γ) (Metric.ball z r)
      = ∫⁻ w in Metric.ball z r, ENNReal.ofReal (weylFactor γ γ w)
          ∂((μ ω).restrict ({0}ᶜ : Set ℂ)) := by
            rw [coneMeasure, withDensity_apply _ Metric.isOpen_ball.measurableSet]
            congr 2
            funext w
            simp only [GMSCase.logSing, sub_zero, weylFactor]
            congr 2
            ring
    _ ≤ ∫⁻ w in Metric.ball z r, ENNReal.ofReal M ∂(μ ω) := by
        apply le_trans (setLIntegral_mono' Metric.isOpen_ball.measurableSet fun w hw =>
          ENNReal.ofReal_le_ofReal (hbound w hw))
        rw [setLIntegral_const, setLIntegral_const]
        exact mul_le_mul_right (Measure.restrict_le_self (Metric.ball z r)) _
    _ = ENNReal.ofReal M * μ ω (Metric.ball z r) := setLIntegral_const _ _
    _ ≤ (ENNReal.ofReal M * C) * ENNReal.ofReal (r ^ κ) := by
        simpa only [mul_assoc] using
          mul_le_mul_right (hb z hz r hr hr1) (ENNReal.ofReal M)

/-- The chosen area of a logarithmically shifted field is the corresponding
cone measure. -/
theorem ae_lqgArea_addLogSing_eq_coneMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC} {γ : ℝ}
    (hX : LQGMetric.IsWholePlaneGFF X P) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, lqgArea γ (GMSCase.addLogSing γ (X ω)) =
      coneMeasure γ (lqgArea γ (X ω)) (fun _ => 0) (GMSCase.logSing γ) := by
  have hcont : ContinuousOn (GMSCase.logSing γ) ({0}ᶜ : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    exact ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz0)).comp
      continuous_norm.continuousAt).neg.const_mul γ |>.continuousWithinAt
  have hmeas : Measurable (GMSCase.logSing γ) := by
    unfold GMSCase.logSing
    exact measurable_const.mul (Real.measurable_log.comp measurable_norm).neg
  have hγQ : γ < lqgQ γ := lt_lqgQ hγ hγ2
  filter_upwards [ae_goodCirc hX, ae_hasScaleCircleAvgs_wp hX,
    ae_hasAreaLimitS_wp hX hγ hγ2, ae_tight_wp hX hγ hγ2 hγ.le hγQ] with ω hg hs ha ht
  have hc : ConeGood γ (X ω) (fun _ => 0) (GMSCase.logSing γ)
      (lqgArea γ (X ω)) γ := by
    refine ⟨hg, hs, ha, measurable_const, hmeas, locallyIntegrable_const 0,
      GMSCase.locallyIntegrable_logSing γ, continuousOn_const, hcont,
      hγ.le, ?_, ht⟩
    refine ⟨0, 1, zero_lt_one, ?_⟩
    intro z _ _
    simp only [GMSCase.logSing, sub_zero, add_zero, le_refl]
  have hz : MatedCRTHarmonic.CellScaling.ofFunC (fun _ => 0) = 0 := Distribution.ofFun_zero
  have heq : X ω - MatedCRTHarmonic.CellScaling.ofFunC (fun _ => 0) +
      MatedCRTHarmonic.CellScaling.ofFunC (GMSCase.logSing γ) =
      GMSCase.addLogSing γ (X ω) := by
    rw [hz, sub_zero]
    rfl
  apply lqgArea_eq_of_hasAreaLimitS
  rw [← heq]
  exact hasAreaLimitS_cone hγ hc

namespace Internal

/-- The compact-center estimate for the logarithmically shifted area, provided
the two descriptions of the original area agree almost surely. -/
theorem ae_forall_compact_center_ball_power_bound_addLogSing_of_area_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P)
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (μ : Ω → Measure ℂ)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P)
    (harea : ∀ᵐ ω ∂P, lqgArea γ (X ω) = μ ω) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P,
      (∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ,
        0 < r → r ≤ 1 → μ ω (Metric.ball z r) ≤ C * ENNReal.ofReal (r ^ κ)) ∧
      ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ r : ℝ,
        0 < r → r ≤ 1 → r ≤ δ →
          lqgArea γ (GMSCase.addLogSing γ (X ω)) (Metric.ball z r) ≤
            C * ENNReal.ofReal (r ^ κ) := by
  obtain ⟨κ, hκ, hb⟩ :=
    ae_forall_compact_center_ball_power_bound_coneMeasure hH hHm hγ hγ2 hp hpq hq μ hμ
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hb, harea, ae_lqgArea_addLogSing_eq_coneMeasure hX hγ hγ2] with ω hb ha hc
  refine ⟨hb.1, ?_⟩
  simpa only [hc, ha] using hb.2

end Internal

end LatticeProb.LQG
