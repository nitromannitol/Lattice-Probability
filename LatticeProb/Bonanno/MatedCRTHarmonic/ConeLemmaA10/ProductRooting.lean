/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.ProductRooting at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingShiftLimit
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingMeasurable

/-!
# Almost-sure identity of the product-space rooting map

For every root in the open unit disk, the final normalization in DMS14 A.10 is almost surely
the identity. This product-space adapter packages the pointwise-in-root statement for an
arbitrary root law supported on the disk.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric

/-- Under any root law supported on the open unit disk, the normalized rooting map agrees almost
everywhere on the field-root product with addition of the exact logarithmic shift. -/
theorem ae_normalizedRootingMap_eq_add_logRootingShift_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z ∈ ball (0 : ℂ) 1) :
    ∀ᵐ p ∂(P.prod ν),
      addConst (h p.1 + logRootingShift γ p.2)
        (-circleAvg (h p.1 + logRootingShift γ p.2) 1 0) =
          h p.1 + logRootingShift γ p.2 := by
  let pred : Ω → ℂ → Prop := fun ω z =>
    addConst (h ω + logRootingShift γ z)
      (-circleAvg (h ω + logRootingShift γ z) 1 0) =
        h ω + logRootingShift γ z
  have hmeas : MeasurableSet {p : Ω × ℂ |
      addConst (h p.1 + logRootingShift γ p.2)
        (-circleAvg (h p.1 + logRootingShift γ p.2) 1 0) =
          h p.1 + logRootingShift γ p.2} := by
    apply measurableSet_eq_fun
    · exact (measurable_normalizedRootingMap γ).comp
        ((hh.1.measurable.comp measurable_fst).prodMk measurable_snd)
    · exact (measurable_add_logRootingShift γ).comp
        ((hh.1.measurable.comp measurable_fst).prodMk measurable_snd)
  haveI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hroot : ∀ᵐ z ∂ν, ∀ᵐ ω ∂P,
      addConst (h ω + logRootingShift γ z)
        (-circleAvg (h ω + logRootingShift γ z) 1 0) =
          h ω + logRootingShift γ z := by
    filter_upwards [hν] with z hz
    exact ae_normalizedRootingMap_eq_add_logRootingShift hh γ hz
  have hfieldRoot : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν,
      addConst (h ω + logRootingShift γ z)
        (-circleAvg (h ω + logRootingShift γ z) 1 0) =
          h ω + logRootingShift γ z :=
    (Measure.ae_ae_comm (μ := P) (ν := ν) (p := pred) (by
      simpa [pred] using hmeas)).2 hroot
  exact (Measure.ae_prod_iff_ae_ae (p := fun p : Ω × ℂ => pred p.1 p.2) (by
    simpa [pred] using hmeas)).2 hfieldRoot

end MatedCRTHarmonic.ConeLemmaA10

