import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.ConeLaw

/-! # Area of a logarithmically singular whole-plane field -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open LQGMetric MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open MatedCRTHarmonic

namespace LatticeProb.LQG

private theorem logSing_continuousOn (γ : ℝ) :
    ContinuousOn (GMSCase.logSing γ) ({0}ᶜ : Set ℂ) := by
  intro z hz
  have hz0 : z ≠ 0 := by simpa using hz
  exact ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz0)).comp
    (continuous_norm.continuousAt)).neg.const_mul γ |>.continuousWithinAt

private theorem logSing_coneGood {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hγ : 0 ≤ γ) (hg : GoodCirc h) (hs : HasScaleCircleAvgs h)
    (ha : HasAreaLimitS γ h μ)
    (ht : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ∫⁻ w in Metric.ball 0 r₀, ENNReal.ofReal (max ‖w‖ s ^ (-(γ * γ))) ∂areaS γ h s ≤
        ENNReal.ofReal ε) :
    ConeGood γ h (fun _ => 0) (GMSCase.logSing γ) μ γ := by
  have hm : Measurable (GMSCase.logSing γ) := by
    unfold GMSCase.logSing
    exact measurable_const.mul (Real.measurable_log.comp measurable_norm).neg
  refine ⟨hg, hs, ha, measurable_const, hm, locallyIntegrable_const 0,
    GMSCase.locallyIntegrable_logSing γ, continuousOn_const, logSing_continuousOn γ,
    hγ, ?_, ht⟩
  refine ⟨0, 1, zero_lt_one, ?_⟩
  intro z _ _
  simp only [GMSCase.logSing, sub_zero, add_zero, le_refl]

private theorem logSing_hasAreaLimitS {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hγ : 0 < γ) (hc : ConeGood γ h (fun _ => 0) (GMSCase.logSing γ) μ γ) :
    HasAreaLimitS γ (GMSCase.addLogSing γ h)
      (coneMeasure γ μ (fun _ => 0) (GMSCase.logSing γ)) := by
  have hz : MatedCRTHarmonic.CellScaling.ofFunC (fun _ => 0) = 0 :=
    Distribution.ofFun_zero
  have heq : h - MatedCRTHarmonic.CellScaling.ofFunC (fun _ => 0) +
      MatedCRTHarmonic.CellScaling.ofFunC (GMSCase.logSing γ) = GMSCase.addLogSing γ h := by
    rw [hz, sub_zero]
    rfl
  rw [← heq]
  exact hasAreaLimitS_cone hγ hc

/-- The subcritical logarithmically singular whole-plane field has a global
continuum area limit. -/
theorem ae_hasAreaLimitS_addLogSing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC} {γ : ℝ}
    (hX : IsWholePlaneGFF X P) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ μ, HasAreaLimitS γ (GMSCase.addLogSing γ (X ω)) μ := by
  have hγQ : γ < lqgQ γ := lt_lqgQ hγ hγ2
  filter_upwards [ae_goodCirc hX, ae_hasScaleCircleAvgs_wp hX,
    ae_hasAreaLimitS_wp hX hγ hγ2, ae_tight_wp hX hγ hγ2 hγ.le hγQ] with ω hg hs ha ht
  exact ⟨_, logSing_hasAreaLimitS hγ (logSing_coneGood hγ.le hg hs ha ht)⟩

end LatticeProb.LQG
