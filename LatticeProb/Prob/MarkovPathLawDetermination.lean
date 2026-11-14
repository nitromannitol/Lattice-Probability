import LatticeProb.Prob.MarkovFiniteDimensionalLaw
import LatticeProb.Bonanno.ReflectedGMS.Limit.PathLawFiniteDimensionalConvergence

/-!
# Determination of Markov path laws

Continuous Markov path-law families with equal transition laws have equal
path laws.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]

/-- A continuous Markov path-law family is determined by its transition laws. -/
theorem markov_pathLaw_eq_of_marginals
    {K L : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (hL : Continuous L)
    (hMK : ∀ z s, MarkovAt K z s) (hML : ∀ z s, MarkovAt L z s)
    (hmarg : ∀ z t, (K z : Measure C(ℝ≥0, E)).map (fun x => x t) =
      (L z : Measure C(ℝ≥0, E)).map (fun x => x t)) (z : E) : K z = L z := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ReflectedGMS.MartingaleLimit.measure_eq_of_forall_map_finsetRestrict_eq
  intro I
  exact map_finsetRestrict_eq_of_markov_marginals hK hL hMK hML hmarg I z

end LatticeProb
