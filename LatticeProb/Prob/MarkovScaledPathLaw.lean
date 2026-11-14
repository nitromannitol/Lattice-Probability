import LatticeProb.Prob.MarkovPathLawDetermination
import LatticeProb.Prob.MarkovTimeScale

/-!
# Time scaling of Markov path laws

Transition laws related by a linear time change determine the corresponding
relation between continuous Markov path laws.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]

/-- If the transition laws agree after a time scaling, then so do the path laws. -/
theorem markov_pathLaw_eq_timeScale_of_marginals
    {K L : E → ProbabilityMeasure C(ℝ≥0, E)} (c : ℝ≥0)
    (hK : Continuous K) (hL : Continuous L)
    (hMK : ∀ z s, MarkovAt K z s) (hML : ∀ z s, MarkovAt L z s)
    (hmarg : ∀ z t, (K z : Measure C(ℝ≥0, E)).map (fun x => x t) =
      (L z : Measure C(ℝ≥0, E)).map (fun x => x (c * t))) (z : E) :
    K z = timeScalePathKernel c L z := by
  apply markov_pathLaw_eq_of_marginals hK (continuous_timeScalePathKernel hL c)
    hMK (fun z t => (hML z (c * t)).timeScalePathKernel hL c t) ?_ z
  intro z t
  rw [hmarg z t]
  change _ = ((L z).map (timeScalePath c) : Measure C(ℝ≥0, E)).map (fun x => x t)
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_map (continuous_eval_const t).measurable
    (continuous_timeScalePath c).measurable]
  rfl

end LatticeProb
