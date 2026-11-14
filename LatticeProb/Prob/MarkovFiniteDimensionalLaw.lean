import LatticeProb.Prob.MarkovFiniteProductLaw
import LatticeProb.Prob.FiniteProductMeasureDetermination

/-!
# Finite-dimensional laws of Markov path families

Equal transition laws determine the finite-dimensional distributions of
continuous Markov path-law families.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal BoundedContinuousFunction

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

/-- Equal transition laws give equal laws at every finite set of times. -/
theorem map_finsetRestrict_eq_of_markov_marginals
    {K L : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (hL : Continuous L)
    (hMK : ∀ z s, MarkovAt K z s) (hML : ∀ z s, MarkovAt L z s)
    (hmarg : ∀ z t, (K z : Measure C(ℝ≥0, E)).map (fun x => x t) =
      (L z : Measure C(ℝ≥0, E)).map (fun x => x t))
    (I : Finset ℝ≥0) (z : E) :
    (K z : Measure C(ℝ≥0, E)).map (fun x : C(ℝ≥0, E) => I.restrict (fun t => x t)) =
      (L z : Measure C(ℝ≥0, E)).map (fun x : C(ℝ≥0, E) => I.restrict (fun t => x t)) := by
  classical
  have hcoord : Continuous (fun x : C(ℝ≥0, E) => I.restrict (fun t => x t)) :=
    continuous_pi fun i => continuous_eval_const (i : ℝ≥0)
  apply measure_eq_of_integral_prod_boundedContinuousFunction_eq
  intro f
  have htest : Continuous (fun x : I → E => ∏ i, f i (x i)) := by
    fun_prop
  rw [integral_map hcoord.measurable.aemeasurable htest.aestronglyMeasurable,
    integral_map hcoord.measurable.aemeasurable htest.aestronglyMeasurable]
  exact integral_finset_prod_eq_of_markov_marginals hK hL hMK hML hmarg I f z

end LatticeProb
