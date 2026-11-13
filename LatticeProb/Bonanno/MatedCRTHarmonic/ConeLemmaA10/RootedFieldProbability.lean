/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.RootedFieldProbability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FieldLawAssembly

/-!
# Probability of the rooted field law

The independent field-root product is a probability measure. Its successive pushforwards by
the ambient rooting map and the field map therefore remain probability measures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMS4.GMSA

/-- The rooted field pushforward supplied by the A.10 input interface is a probability measure. -/
theorem WholePlaneRootingFieldLawInputs.rootedFieldLaw_isProbability
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω) :
    IsProbabilityMeasure (D.rootedLaw.map D.field) := by
  letI : IsProbabilityMeasure D.unrootedLaw :=
    D.normalizedWPGFF.1.gaussian.isProbabilityMeasure
  have hrooted : IsProbabilityMeasure D.rootedLaw := by
    rw [D.rootedLaw_eq_rootSample_map]
    exact (Measure.isProbabilityMeasure_map_iff
      D.rootSample_measurable.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure D.rootedLaw := hrooted
  exact (Measure.isProbabilityMeasure_map_iff
    D.normalizedWPGFF.1.measurable.aemeasurable).2 inferInstance

end MatedCRTHarmonic.ConeLemmaA10

