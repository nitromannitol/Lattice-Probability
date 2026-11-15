import LatticeProb.LQG.NormalizedSpliceAreaMeasurable

/-! # Independence of a logarithmically singular field and its area -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric MatedCRTHarmonic MatedCRTHarmonic.CellScaling

namespace LatticeProb.LQG

/-- Adjoining the selected area of a logarithmically singular whole-plane GFF
preserves its joint independence with an auxiliary random variable. -/
theorem indepFun_logSingular_field_area_aux
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} {γ : ℝ} {Y : Ω → DistC} {W : Ω → A} {Z : Ω → B}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hY : IsWholePlaneGFF Y P)
    (hW : Measurable W) (hZ : Measurable Z)
    (hind : IndepFun (fun ω => (Y ω, W ω)) Z P) :
    IndepFun (fun ω => ((GMSCase.addLogSing γ (Y ω),
      lqgArea γ (GMSCase.addLogSing γ (Y ω))), W ω)) Z P := by
  have hpair : Measurable (fun ω => (Y ω, W ω)) := hY.measurable.prodMk hW
  have harea : AEMeasurable (fun h : DistC => lqgArea γ (GMSCase.addLogSing γ h))
      (P.map Y) :=
    aemeasurable_area_addLogSing hγ hγ2 (LQGMetric.GM.isWholePlaneGFF_id_map hY)
  have hmarg : (P.map (fun ω => (Y ω, W ω))).map Prod.fst = P.map Y := by
    rw [Measure.map_map measurable_fst hpair]
    rfl
  have harea' : AEMeasurable
      (fun p : DistC × A => lqgArea γ (GMSCase.addLogSing γ p.1))
      (P.map (fun ω => (Y ω, W ω))) := by
    have harea₁ : AEMeasurable (fun h : DistC =>
        lqgArea γ (GMSCase.addLogSing γ h))
        ((P.map (fun ω => (Y ω, W ω))).map Prod.fst) := by
      rw [hmarg]
      exact harea
    exact harea₁.comp_measurable measurable_fst
  have hfield : Measurable (fun p : DistC × A => GMSCase.addLogSing γ p.1) :=
    (GMSCase.measurable_addLogSing γ).comp measurable_fst
  have htransform : AEMeasurable
      (fun p : DistC × A => ((GMSCase.addLogSing γ p.1,
        lqgArea γ (GMSCase.addLogSing γ p.1)), p.2))
      (P.map (fun ω => (Y ω, W ω))) :=
    (hfield.aemeasurable.prodMk harea').prodMk measurable_snd.aemeasurable
  exact hind.comp₀ hpair.aemeasurable hZ.aemeasurable htransform measurable_id.aemeasurable

end LatticeProb.LQG
