/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.RootingSampleIntegral at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FieldLawAssembly

/-!
# Rooted-field cylinder integrals on the independent sample space

This file rewrites a cylinder expectation under the rooted field law as the corresponding
expectation over the independent unrooted-field and root sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMS4.GMSA
open LQGMetric LQGMetric.GFFInv

/-- A continuous finite-cylinder observable under the rooted field law can be evaluated on the
independent field-root sample through the normalized rooting map. -/
theorem WholePlaneRootingFieldLawInputs.integral_cylinder_rooted_eq_rootSample
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω)
    (I : Finset TestC0) (F : (I → ℝ) → ℝ) (hF : Continuous F) :
    (∫ g, F (I.restrict (GFFLaw.ev0 g)) ∂(D.rootedLaw.map D.field)) =
      ∫ p : Ω × ℂ,
        F (I.restrict (GFFLaw.ev0
          (addConst (D.field p.1 + logRootingShift D.gamma p.2)
            (-circleAvg (D.field p.1 + logRootingShift D.gamma p.2) 1 0))))
        ∂(D.unrootedLaw.prod normalizedLebesgueOnRootingDisk) := by
  rw [D.rootedFieldLaw_eq_rootingMap]
  exact integral_map
    ((measurable_normalizedRootingMap D.gamma).comp
      ((D.normalizedWPGFF.1.measurable.comp measurable_fst).prodMk
        measurable_snd)).aemeasurable
    ((hF.measurable.comp ((Finset.measurable_restrict I).comp
      (measurable_pi_iff.2 fun ψ => measurable_pair ψ.1))).aestronglyMeasurable)

end MatedCRTHarmonic.ConeLemmaA10

