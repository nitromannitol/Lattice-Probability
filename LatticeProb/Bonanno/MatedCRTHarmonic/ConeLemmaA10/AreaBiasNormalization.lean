/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.AreaBiasNormalization at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FieldLawAssembly

/-!
# Explicit normalization of the whole-plane area bias

The field-law identity in DMS14 Lemma A.10 weights a normalized whole-plane GFF by its
unit-disk quantum area divided by its expectation. The expectation was computed in
`FieldLawAssembly` to be exactly `π`. This file records the small adapter from that abstract
normalization to the explicit density used by the final field-law assembly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMS4.GMSA

/-- The normalized unit-disk area density has the explicit denominator `π`, pointwise. -/
theorem WholePlaneRootingFieldLawInputs.areaBiasDensity_eq_div_pi
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω) :
    (fun ω => D.area.unitDiskMass ω / D.expectedUnitDiskMass) =
      fun ω => D.area.unitDiskMass ω / ENNReal.ofReal Real.pi := by
  rw [WholePlaneRootingFieldLawInputs.expectedUnitDiskMass,
    MatedCRTHarmonic.ConeLemmaA10.WholePlaneGMCUnitDiskArea.expectedUnitDiskMass_eq_pi
      D.area D.gamma_pos D.gamma_lt_two]

/-- Replacing the abstract expected-mass denominator by `π` does not change the
area-biased measure. -/
theorem WholePlaneRootingFieldLawInputs.withDensity_areaBias_eq_div_pi
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω) :
    D.unrootedLaw.withDensity
        (fun ω => D.area.unitDiskMass ω / D.expectedUnitDiskMass) =
      D.unrootedLaw.withDensity
        (fun ω => D.area.unitDiskMass ω / ENNReal.ofReal Real.pi) := by
  rw [D.areaBiasDensity_eq_div_pi]

/-- The explicitly normalized area-biased law has total mass one. -/
theorem WholePlaneRootingFieldLawInputs.withDensity_div_pi_isProbability
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω) :
    IsProbabilityMeasure
      (D.unrootedLaw.withDensity
        (fun ω => D.area.unitDiskMass ω / ENNReal.ofReal Real.pi)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const'' _ D.area.unitDiskMass_aemeasurable]
  rw [MatedCRTHarmonic.ConeLemmaA10.WholePlaneGMCUnitDiskArea.expectedUnitDiskMass_eq_pi
    D.area D.gamma_pos D.gamma_lt_two]
  exact ENNReal.mul_inv_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr Real.pi_pos)) ENNReal.ofReal_ne_top

end MatedCRTHarmonic.ConeLemmaA10

