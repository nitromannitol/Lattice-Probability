import LatticeProb.Prob.MarkovOrderedIncrements

/-!
# Product expectations at ordered observation times

Continuous Markov path-law families with equal one-time transition laws have
matching product expectations at ordered observation times.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

/-- Equal one-time transition laws determine product expectations at any
nondecreasing list of observation times. -/
theorem integral_ordered_list_prod_eq_of_markov_marginals
    {K L : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (hL : Continuous L)
    (hMK : ∀ z s, MarkovAt K z s) (hML : ∀ z s, MarkovAt L z s)
    (hmarg : ∀ z t, (K z : Measure C(ℝ≥0, E)).map (fun x => x t) =
      (L z : Measure C(ℝ≥0, E)).map (fun x => x t))
    (tests : List (ℝ≥0 × (E →ᵇ ℝ)))
    (hs : tests.Pairwise (fun p q => p.1 ≤ q.1)) (z : E) :
    ∫ x, ((tests.map fun p => p.2 (x p.1)).prod) ∂(K z : Measure C(ℝ≥0, E)) =
      ∫ x, ((tests.map fun p => p.2 (x p.1)).prod) ∂(L z : Measure C(ℝ≥0, E)) := by
  let increments := orderedTimeIncrements 0 tests
  have hc : cumulativeTests 0 increments = tests :=
    cumulativeTests_orderedTimeIncrements 0 tests (fun _ _ => zero_le) hs
  have htest (x : C(ℝ≥0, E)) :
      orderedProductTest increments x = (tests.map fun p => p.2 (x p.1)).prod := by
    have hshift : pathShift x 0 = x := by
      ext t
      simp only [pathShift_apply, zero_add]
    have h := orderedProductTest_pathShift_eq_prod increments 0 x
    rw [hshift, hc] at h
    exact h
  simpa only [htest] using
    integral_orderedProductTest_eq_of_markov_marginals hK hL hMK hML hmarg increments z

end LatticeProb
