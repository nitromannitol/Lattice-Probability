import LatticeProb.LQG.InsertedAreaCurveNull
import LatticeProb.LQG.ConeAreaRandomMeasure
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPArea

/-! # Field-independent traces and logarithmically inserted area -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric MatedCRTHarmonic LatticeProb.Gauss
open LatticeProb.LQG.LQGMeasureNonatomicMass

namespace LatticeProb.LQG

/-- A compact-time Lebesgue-null trace independent of a whole-plane field has
zero logarithmically inserted area in the unit disk, when the circle
coordinates represent the same field at the dyadic scales. -/
theorem ae_lqgArea_addLogSing_trace_eq_zero_of_indep_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hcircle : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂volume,
      hcirc ω (dyadicScale k) z = circleAvg (X ω) (dyadicScale k) z)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g) (hind : IndepFun g X P)
    {T : Set ℝ} (hT : IsCompact T) (hnull : ∀ᵐ ω ∂P, volume (g ω '' T) = 0) :
    ∀ᵐ ω ∂P, CellScaling.lqgArea γ (GMSCase.addLogSing α (X ω))
      ((g ω '' T) ∩ ball (0 : ℂ) 1) = 0 := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := lqgMeasureExistenceLP_proved P γ 0 hC hcirc hh hγ0 hγ2 hQ
  have hμ₀' : IsLQGMeasure P γ hcirc μ₀ := by
    simpa only [IsLQGMeasureOfField, fieldCircleAverage_zero_lp] using hμ₀
  have heq : (fun ω => CellScaling.lqgArea γ (X ω)) =ᵐ[P] μ₀ :=
    ae_lqgArea_eq_of_isLQGMeasure_ae hμ₀' hcircle
  have hid := LQGMetric.GM.isWholePlaneGFF_id_map hX
  let : IsProbabilityMeasure (P.map X) := hid.gaussian.isProbabilityMeasure
  have harea : AEMeasurable (CellScaling.lqgArea γ) (P.map X) := by
    apply LatticeProb.aemeasurable_lqgArea_of_ae_vagueLimit measurable_id.aemeasurable
    exact MatedCRTHarmonic.LQGCoord.ae_exists_isVagueLimitC_wp hid hγ0 hγ2
  have hareaX : AEMeasurable (fun ω => CellScaling.lqgArea γ (X ω)) P :=
    harea.comp_aemeasurable hX.measurable.aemeasurable
  have hμ₀m : AEMeasurable μ₀ P := hareaX.congr heq
  have hind₀ : IndepFun g μ₀ P := by
    have h := hind.comp₀ hgm.aemeasurable hX.measurable.aemeasurable
      measurable_id.aemeasurable harea
    exact h.congr Filter.EventuallyEq.rfl heq
  exact ae_lqgArea_addLogSing_trace_inter_unitBall_eq_zero hX hh hcircle hγ0 hγ2 hα
    hμ₀ hμ₀m hgm hind₀ hT hnull

end LatticeProb.LQG
