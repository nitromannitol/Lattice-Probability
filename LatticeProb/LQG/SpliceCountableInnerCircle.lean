import LatticeProb.LQG.SpliceInnerCircle

/-! # Countable inner circle averages of a Brownian radial splice -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic.GMCFacts

namespace LatticeProb.LQG

/-- On one almost-sure event, the inner circle readout holds at all times in
any given countable set. The exterior path may depend on the field and inner
path. -/
theorem ae_circleAvg_replField_twoSided_inner_on_countable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (W V : Ω → C(ℝ≥0, ℝ))
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    (S : Set ℝ≥0) (hS : S.Countable) :
    ∀ᵐ ω ∂P, ∀ t ∈ S,
      circleAvg (replField X (fun ω => twoSided (W ω) (V ω)) ω)
        (Real.exp (-(t : ℝ))) 0 = W ω t := by
  exact (ae_ball_iff hS).2 fun t _ =>
    ae_circleAvg_replField_twoSided_inner hX hB W V hW t

end LatticeProb.LQG
