import LatticeProb.LQG.InsertedCurveNull
import LatticeProb.LQG.LogInsertionAreaBridge
import LatticeProb.LQG.LQGMeasureExistenceProved

/-! # Independent traces and logarithmically inserted distribution-valued fields -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric MatedCRTHarmonic LatticeProb.Gauss

namespace LatticeProb.LQG

/-- If the circle coordinates represent the same distribution-valued field, a
Lebesgue-null compact-time trace independent of its uninserted quantum area
has zero selected logarithmically inserted quantum area in the unit disk. -/
theorem ae_lqgArea_addLogSing_trace_inter_unitBall_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hcircle : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂volume,
      hcirc ω (dyadicScale k) z = circleAvg (X ω) (dyadicScale k) z)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {μ₀ : Ω → Measure ℂ} (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hμ₀m : AEMeasurable μ₀ P) {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g)
    (hind : IndepFun g μ₀ P) {T : Set ℝ} (hT : IsCompact T)
    (hnull : ∀ᵐ ω ∂P, volume (g ω '' T) = 0) :
    ∀ᵐ ω ∂P, CellScaling.lqgArea γ (GMSCase.addLogSing α (X ω))
      ((g ω '' T) ∩ ball (0 : ℂ) 1) = 0 := by
  obtain ⟨μ, hμ⟩ := lqgMeasureExistenceLP_proved P γ α hC hcirc hh hγ0 hγ2 hα
  have htrace := ae_inserted_lqgMeasure_trace_inter_unitBall_eq_zero hh hγ0 hγ2 hα
    hμ hμ₀ hμ₀m hgm hind hT hnull
  have heq : ∀ᵐ ω ∂P, CellScaling.lqgArea γ (GMSCase.addLogSing α (X ω)) = μ ω := by
    apply ae_lqgArea_eq_of_isLQGMeasure_ae hμ
    filter_upwards [hcircle, ae_logInsertion_circleAvg hX α] with ω hc hl k
    filter_upwards [hc k, hl (dyadicScale k) (by unfold dyadicScale; positivity)] with z hc' hl'
    rw [← hl']
    simp only [fieldCircleAverage, hc']
  filter_upwards [heq, htrace] with ω heqω htraceω
  rw [heqω]
  exact htraceω

end LatticeProb.LQG
