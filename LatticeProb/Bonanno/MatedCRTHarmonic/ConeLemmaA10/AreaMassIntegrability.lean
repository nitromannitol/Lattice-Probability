/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.AreaMassIntegrability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.AreaExactMass

/-!
# Integrability of the unit-disk LQG area mass

This file packages the integrability consequence of the exact unit-disk first moment.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Metric

namespace MatedCRTHarmonic.ConeLemmaA10

/-- The real-valued mass of the open unit disk is integrable for an `IsLQGAreaOf` limit. -/
theorem integrable_areaMeasure_unitDisk_toReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H : ℝ → ℂ → Ω → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H μ P) :
    Integrable (fun ω => (μ ω (ball (0 : ℂ) 1)).toReal) P := by
  have hmass := lintegral_areaMeasure_unitDisk_eq hH hHm hγ hγ2 hμ
  exact integrable_toReal_of_lintegral_ne_top hmass.1
    (by rw [hmass.2]; exact measure_ball_lt_top.ne)

end MatedCRTHarmonic.ConeLemmaA10

