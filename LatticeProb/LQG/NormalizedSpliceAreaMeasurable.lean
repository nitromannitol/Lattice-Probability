import LatticeProb.LQG.NormalizedSpliceArea
import LatticeProb.LQG.ConeAreaRandomMeasure

/-! # Measurability of a normalized radial splice and its area -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord

namespace LatticeProb.LQG

/-- The selected subcritical area of a logarithmically singular whole-plane
GFF is an almost everywhere measurable random measure. -/
theorem aemeasurable_area_addLogSing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} {X : Ω → DistC}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsWholePlaneGFF X P) :
    AEMeasurable (fun ω => lqgArea γ (GMSCase.addLogSing γ (X ω))) P := by
  apply LatticeProb.aemeasurable_lqgArea_of_ae_vagueLimit
  · exact ((GMSCase.measurable_addLogSing γ).comp hX.measurable).aemeasurable
  · filter_upwards [ae_hasAreaLimitS_addLogSing hX hγ hγ2] with ω ⟨μ, hμ⟩
    exact ⟨μ, ⟨hμ.1, fun f hf hfc => (hμ.2 f hf hfc).comp tendsto_dyadicScale⟩⟩

/-- The logarithmically singular normalized radial splice and its selected
area form an almost everywhere measurable pair on the original space. -/
theorem aemeasurable_normalized_splice_field_area
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X : Ω → DistC} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsWholePlaneGFF X P)
    {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hW : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P) :
    let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
    let F : Ω → DistC := fun ω => GMSCase.addLogSing γ
      (replField X (fun ω => twoSided (W ω) (V ω)) ω)
    AEMeasurable (fun ω => (F ω, lqgArea γ (F ω))) P := by
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  let Y : Ω → DistC := replField X (fun ω => twoSided (W ω) (V ω))
  have hY : IsWholePlaneGFF Y P :=
    (IsWholePlaneGFF.normalized_replField_twoSided hX hRm hR hWm hW hXW).1
  have hF : AEMeasurable (fun ω => GMSCase.addLogSing γ (Y ω)) P :=
    ((GMSCase.measurable_addLogSing γ).comp hY.measurable).aemeasurable
  exact hF.prodMk (aemeasurable_area_addLogSing hγ hγ2 hY)

end LatticeProb.LQG
