/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.AEMeasurable
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCTendsto
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.Metrizable
import LatticeProb.Bonanno.SLUMetricAPI2
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.LFPP
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreB
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P6A

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem exists_measurable_continuous_real_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℂ → ℝ)
    (hFm : Measurable F)
    (hFc : ∀ᵐ ω ∂P, Continuous (F ω)) :
    ∃ G : Ω → C(ℂ, ℝ),
      Measurable G ∧ ∀ᵐ ω ∂P, (G ω : ℂ → ℝ) = F ω := by
  classical
  obtain ⟨B, hBae, hBm, hBsub⟩ :=
    IsMeasurablyGenerated.exists_measurable_subset hFc
  let G : Ω → C(ℂ, ℝ) := fun ω =>
    if hω : ω ∈ B then ⟨F ω, hBsub hω⟩
    else ⟨fun _ => 0, continuous_const⟩
  refine ⟨G, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro q
    have heq : (fun ω => G ω q) =
        (fun ω => if ω ∈ B then F ω q else (0 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ B <;> simp [G, hω]
    rw [heq]
    exact (measurable_pi_iff.mp hFm q).ite hBm measurable_const
  · have hBae' : ∀ᵐ ω ∂P, ω ∈ B := hBae
    filter_upwards [hBae'] with ω hω
    simp [G, hω]

 

theorem aemeasurable_heat_smoothing_version
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (δ : Set.Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h δ X) :
    AEMeasurable X P := by
  have hHm : Measurable (fun ω : Ω => heatMollify (δ : ℝ) (h ω)) :=
    measurable_pi_iff.mpr fun z =>
      (measurable_heatMollify_left (δ : ℝ) z).comp hh.1.measurable
  have hHc : ∀ᵐ ω ∂P, Continuous (heatMollify (δ : ℝ) (h ω)) :=
    (hh.1.ae_tendstoLocallyUniformly_heatMollify (δ : ℝ) δ.property.ne').mono
      fun _ hω => hω.2
  obtain ⟨G, hGm, hGeq⟩ :=
    exists_measurable_continuous_real_version P
      (fun ω => heatMollify (δ : ℝ) (h ω)) hHm hHc
  have hXeq := DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh δ X hX
  apply hGm.aemeasurable.congr
  filter_upwards [hGeq, hXeq] with ω hGω hXω
  apply ContinuousMap.ext
  intro z
  exact (congrFun hGω z).trans (hXω z).symm

end SupercriticalLQGUniqueness.B2.PfeAxioms
