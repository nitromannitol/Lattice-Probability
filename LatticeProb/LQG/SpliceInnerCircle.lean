import LatticeProb.LQG.SpliceCircleAverage
import LatticeProb.LQG.SpliceRadialIntegrability

/-! # Inner circle averages of a Brownian radial splice -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic.GMCFacts

namespace LatticeProb.LQG

/-- At each fixed nonnegative time, the circle average of a radial replacement
with a Brownian inner path equals that path. The exterior path is arbitrary;
the exceptional event may depend on the time. -/
theorem ae_circleAvg_replField_twoSided_inner
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (W V : Ω → C(ℝ≥0, ℝ))
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) (t : ℝ≥0) :
    ∀ᵐ ω ∂P,
      circleAvg (replField X (fun ω => twoSided (W ω) (V ω)) ω)
        (Real.exp (-(t : ℝ))) 0 = W ω t := by
  have hi := ae_locallyIntegrable_radialW_twoSided hB W V hW
  have hc := ae_circleAvg_replField hX (fun ω => twoSided (W ω) (V ω)) hi
    (Real.exp_pos (-(t : ℝ)))
  filter_upwards [hc, hW, hB.eval_zero_ae_eq_zero] with ω hc hw hz
  have hwzero : W ω 0 = 0 := (hw 0).trans hz
  rw [hc, Real.log_exp, neg_neg, twoSided_apply,
    Real.toNNReal_coe, Real.toNNReal_of_nonpos (neg_nonpos.mpr t.coe_nonneg),
    sub_self, add_zero, hwzero, sub_zero]

end LatticeProb.LQG
