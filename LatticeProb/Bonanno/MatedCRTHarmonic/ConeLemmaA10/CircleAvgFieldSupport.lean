/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CircleAvgFieldSupport at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.ProductRooting
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CircleAvgLawExtensionality

/-!
# Circle-average support for rooted and area-biased fields

The extensionality theorem for `DistC` laws requires almost-sure convergence of the defining
mollified averages and zero unit-circle average. This file packages that support for the rooted
field law and records its preservation under area bias.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

/-- The support condition required by circle-average law extensionality. -/
def CircleAvgFieldSupport (g : DistC) : Prop :=
  (∃ a, Tendsto (fun n => mollAvg g n 0 1) atTop (𝓝 a)) ∧ circleAvg g 1 0 = 0

/-- The circle-average support condition is measurable on the cylinder field space. -/
theorem measurableSet_circleAvgFieldSupport :
    MeasurableSet {g : DistC | CircleAvgFieldSupport g} := by
  have hconv : MeasurableSet {g : DistC |
      Tendsto (fun n => mollAvg g n 0 1) atTop (𝓝 (circleAvg g 1 0))} := by
    apply MeasureTheory.measurableSet_tendsto_fun
    · intro n
      have heq : (fun g : DistC => mollAvg g n 0 1) =
          fun g => g (CircleAvg.circBump n 0 1) := by
        funext g
        exact CircleAvg.mollAvg_eq g n 0 1
      rw [heq]
      exact measurable_evalDist _
    · exact measurable_circleAvg_left 1 0
  have hzero : MeasurableSet {g : DistC | circleAvg g 1 0 = 0} :=
    measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const
  have hEq : {g : DistC | CircleAvgFieldSupport g} =
      {g : DistC | Tendsto (fun n => mollAvg g n 0 1) atTop
        (𝓝 (circleAvg g 1 0)) ∧ circleAvg g 1 0 = 0} := by
    ext g
    constructor
    · rintro ⟨⟨a, ha⟩, hzero⟩
      have hlim : circleAvg g 1 0 = a := CircleAvg.circleAvg_eq_of_tendsto ha
      change Tendsto (fun n => mollAvg g n 0 1) atTop (𝓝 (circleAvg g 1 0)) ∧
        circleAvg g 1 0 = 0
      rw [hlim]
      exact ⟨ha, hlim.symm.trans hzero⟩
    · rintro ⟨ha, hzero⟩
      exact ⟨⟨circleAvg g 1 0, ha⟩, hzero⟩
  rw [hEq]
  exact hconv.inter hzero

/-- Adding the logarithmic rooting shift preserves convergence of the unit-circle mollified
averages on the field-root product. -/
theorem ae_tendsto_mollAvg_add_logRootingShift_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z ∈ ball (0 : ℂ) 1) :
    ∀ᵐ p ∂(P.prod ν), ∃ a,
      Tendsto (fun n => mollAvg (h p.1 + logRootingShift γ p.2) n 0 1) atTop (𝓝 a) := by
  haveI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hfield : ∀ᵐ p ∂(P.prod ν),
      ∃ a, Tendsto (fun n => mollAvg (h p.1) n 0 1) atTop (𝓝 a) :=
    Measure.quasiMeasurePreserving_fst.ae (CircleAvg.ae_tendsto_mollAvg hh.1 0 one_pos)
  have hroot : ∀ᵐ p ∂(P.prod ν), p.2 ∈ ball (0 : ℂ) 1 :=
    Measure.quasiMeasurePreserving_snd.ae hν
  filter_upwards [hfield, hroot] with p ⟨a, ha⟩ hz
  refine ⟨a, ?_⟩
  have hshift := tendsto_mollAvg_logRootingShift (γ := γ) hz
  have hadd : Tendsto
      (fun n => mollAvg (h p.1 + logRootingShift γ p.2) n 0 1) atTop (𝓝 (a + 0)) := by
    simpa only [mollAvg_add] using ha.add hshift
  simpa using hadd

/-- The normalized rooted field has the support required by circle-average law extensionality,
almost surely on the independent field-root product. -/
theorem ae_circleAvgFieldSupport_normalizedRootingMap_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z ∈ ball (0 : ℂ) 1) :
    ∀ᵐ p ∂(P.prod ν),
      CircleAvgFieldSupport
        (addConst (h p.1 + logRootingShift γ p.2)
          (-circleAvg (h p.1 + logRootingShift γ p.2) 1 0)) := by
  let raw : Ω × ℂ → DistC := fun p => h p.1 + logRootingShift γ p.2
  have hconv := ae_tendsto_mollAvg_add_logRootingShift_prod hh γ hν
  haveI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  let pred : Ω → ℂ → Prop := fun ω z => circleAvg (h ω + logRootingShift γ z) 1 0 = 0
  have hpred : MeasurableSet {p : Ω × ℂ | pred p.1 p.2} := by
    apply measurableSet_eq_fun
    · exact (measurable_circleAvg_left 1 0).comp <|
        (measurable_add_logRootingShift γ).comp
          ((hh.1.measurable.comp measurable_fst).prodMk measurable_snd)
    · exact measurable_const
  have hzeroRoot : ∀ᵐ z ∂ν, ∀ᵐ ω ∂P, pred ω z := by
    filter_upwards [hν] with z hz
    exact ae_circleAvg_add_logRootingShift_eq_zero hh γ hz
  have hzeroField : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν, pred ω z :=
    (Measure.ae_ae_comm (μ := P) (ν := ν) (p := pred) hpred).2 hzeroRoot
  have hzero : ∀ᵐ p ∂(P.prod ν), circleAvg (raw p) 1 0 = 0 :=
    (Measure.ae_prod_iff_ae_ae (p := fun p : Ω × ℂ => pred p.1 p.2) (by
      simpa only [pred] using hpred)).2 hzeroField
  have hmapEq := ae_normalizedRootingMap_eq_add_logRootingShift_prod hh γ hν
  filter_upwards [hconv, hzero, hmapEq] with p ⟨a, ha⟩ hz hEq
  refine ⟨⟨a, ?_⟩, ?_⟩
  · simpa only [hEq] using ha
  · rw [hEq]
    exact hz

/-- The field law of the normalized rooted map has circle-average support. -/
theorem ae_circleAvgFieldSupport_map_normalizedRootingMap
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z ∈ ball (0 : ℂ) 1) :
    ∀ᵐ g ∂((P.prod ν).map fun p : Ω × ℂ =>
      addConst (h p.1 + logRootingShift γ p.2)
        (-circleAvg (h p.1 + logRootingShift γ p.2) 1 0)),
      CircleAvgFieldSupport g := by
  have hmeas : Measurable (fun p : Ω × ℂ =>
      addConst (h p.1 + logRootingShift γ p.2)
        (-circleAvg (h p.1 + logRootingShift γ p.2) 1 0)) :=
    (measurable_normalizedRootingMap γ).comp
      ((hh.1.measurable.comp measurable_fst).prodMk measurable_snd)
  rw [ae_map_iff hmeas.aemeasurable measurableSet_circleAvgFieldSupport]
  exact ae_circleAvgFieldSupport_normalizedRootingMap_prod hh γ hν

/-- A field law obtained by weighting the underlying samples with a density remains supported
on fields with convergent, zero-average unit-circle mollifications. This applies in particular
to the normalized area-biased law. -/
theorem ae_circleAvgFieldSupport_map_withDensity
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (w : Ω → ℝ≥0∞) :
    ∀ᵐ g ∂((P.withDensity w).map h), CircleAvgFieldSupport g := by
  rw [ae_map_iff hh.1.measurable.aemeasurable measurableSet_circleAvgFieldSupport]
  have hsource : ∀ᵐ ω ∂P, CircleAvgFieldSupport (h ω) := by
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hh.1 0 one_pos, hh.2] with ω ⟨a, ha⟩ hz
    exact ⟨⟨a, ha⟩, hz⟩
  exact (withDensity_absolutelyContinuous P w).ae_le hsource

end MatedCRTHarmonic.ConeLemmaA10

