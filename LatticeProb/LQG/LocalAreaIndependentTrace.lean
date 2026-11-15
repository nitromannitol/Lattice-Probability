import LatticeProb.LQG.FieldIndependentInsertedTrace

/-! # Independent traces for locally identified quantum areas -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric MatedCRTHarmonic LatticeProb.Gauss
open LatticeProb.LQG.LQGMeasureNonatomicMass

namespace LatticeProb.LQG

/-- A measure agreeing locally with inserted quantum area does not charge an
independent compact-time Lebesgue-null trace inside the unit disk. -/
theorem ae_localArea_trace_eq_zero_of_indep_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hcircle : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂volume,
      hcirc ω (dyadicScale k) z = circleAvg (X ω) (dyadicScale k) z)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g) (hind : IndepFun g X P)
    {T : Set ℝ} (hT : IsCompact T) (hnull : ∀ᵐ ω ∂P, volume (g ω '' T) = 0)
    {ν : Ω → Measure ℂ}
    (hloc : ∀ᵐ ω ∂P, (ν ω).restrict (ball (0 : ℂ) 1) =
      (CellScaling.lqgArea γ (GMSCase.addLogSing α (X ω))).restrict (ball 0 1)) :
    ∀ᵐ ω ∂P, ν ω ((g ω '' T) ∩ ball (0 : ℂ) 1) = 0 := by
  have htrace := ae_lqgArea_addLogSing_trace_eq_zero_of_indep_field
    hX hh hcircle hγ0 hγ2 hα hgm hind hT hnull
  filter_upwards [htrace, hloc] with ω ht hl
  have hmeas : MeasurableSet (g ω '' T) := (hT.image (g ω).continuous).isClosed.measurableSet
  have heq := congrArg (fun μ : Measure ℂ => μ (g ω '' T)) hl
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hmeas] at heq
  exact heq.trans ht

end LatticeProb.LQG
