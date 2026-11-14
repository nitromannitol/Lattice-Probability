import LatticeProb.Prob.MarkovPrependLaw

/-!
# Ordered product tests for Markov path laws

Continuous Markov path-law families with equal one-time transition laws agree
on all products of bounded continuous tests at ordered times.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

/-- Product of position tests at the successive sums of the given time increments. -/
noncomputable def orderedProductTest :
    List (ℝ≥0 × (E →ᵇ ℝ)) → (C(ℝ≥0, E) →ᵇ ℝ)
  | [] => 1
  | (s, f) :: rest =>
      f.compContinuous ⟨fun x => x s, continuous_eval_const s⟩ *
        (orderedProductTest rest).compContinuous
          ⟨fun x => pathShift x s,
            continuous_pathShift_uncurry.comp (continuous_id.prodMk continuous_const)⟩

/-- Equal one-time transition laws determine all ordered product expectations. -/
theorem integral_orderedProductTest_eq_of_markov_marginals
    {K L : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (hL : Continuous L)
    (hMK : ∀ z s, MarkovAt K z s) (hML : ∀ z s, MarkovAt L z s)
    (hmarg : ∀ z t, (K z : Measure C(ℝ≥0, E)).map (fun x => x t) =
      (L z : Measure C(ℝ≥0, E)).map (fun x => x t))
    (tests : List (ℝ≥0 × (E →ᵇ ℝ))) (z : E) :
    ∫ x, orderedProductTest tests x ∂(K z : Measure C(ℝ≥0, E)) =
      ∫ x, orderedProductTest tests x ∂(L z : Measure C(ℝ≥0, E)) := by
  induction tests generalizing z with
  | nil => simp [orderedProductTest]
  | cons p rest ih =>
    rcases p with ⟨s, f⟩
    change (∫ x, f (x s) * orderedProductTest rest (pathShift x s)
      ∂(K z : Measure C(ℝ≥0, E))) =
      ∫ x, f (x s) * orderedProductTest rest (pathShift x s)
        ∂(L z : Measure C(ℝ≥0, E))
    exact integral_eval_mul_shift_eq_of_markov_marginals hK hL hMK hML hmarg
      (orderedProductTest rest) (fun y => ih y) z s f

end LatticeProb
