/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.RootingRawShiftIntegral at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingCylinderObservable
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingSampleIntegral

/-!
# Rooted-field cylinder integrals before final normalization

The mean-zero cylinder coordinates do not see the additive constant used in the final
circle-average normalization. This file records the resulting raw-shift integral identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMS4.GMSA
open LQGMetric LQGMetric.GFFInv

/-- A continuous finite `ev0` cylinder under the rooted field law can be evaluated directly on
the unnormalized logarithmically shifted independent field-root sample. -/
theorem WholePlaneRootingFieldLawInputs.integral_cylinder_rooted_eq_rawShift
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω)
    (I : Finset TestC0) (F : (I → ℝ) → ℝ) (hF : Continuous F) :
    (∫ g, F (I.restrict (GFFLaw.ev0 g)) ∂(D.rootedLaw.map D.field)) =
      ∫ p : Ω × ℂ,
        F (I.restrict (GFFLaw.ev0
          (D.field p.1 + logRootingShift D.gamma p.2)))
        ∂(D.unrootedLaw.prod normalizedLebesgueOnRootingDisk) := by
  rw [D.integral_cylinder_rooted_eq_rootSample I F hF]
  apply integral_congr_ae
  filter_upwards with p
  exact congrArg (fun q => F (I.restrict q))
    (pair0_addConst_eq
      (D.field p.1 + logRootingShift D.gamma p.2)
      (-circleAvg (D.field p.1 + logRootingShift D.gamma p.2) 1 0))

end MatedCRTHarmonic.ConeLemmaA10

