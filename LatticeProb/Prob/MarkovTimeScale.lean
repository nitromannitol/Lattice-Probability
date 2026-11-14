import LatticeProb.Prob.MarkovAtMap
import LatticeProb.Prob.PathSpaceScaling

/-!
# Linear time changes of Markov path kernels

A continuous family of Markov path laws remains continuous and Markov after a
nonnegative linear change of time.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)] in
/-- Linear time changes are continuous in the compact-open topology. -/
theorem continuous_timeScalePath (c : ℝ≥0) :
    Continuous (timeScalePath c : C(ℝ≥0, E) → C(ℝ≥0, E)) :=
  ContinuousMap.continuous_precomp _

/-- The family obtained by changing the time scale of each path law. -/
noncomputable def timeScalePathKernel (c : ℝ≥0) (K : E → ProbabilityMeasure C(ℝ≥0, E)) :
    E → ProbabilityMeasure C(ℝ≥0, E) :=
  fun z => (K z).map (timeScalePath c)

omit [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- Linear time changes preserve continuity of a family of path laws. -/
theorem continuous_timeScalePathKernel {K : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) (c : ℝ≥0) : Continuous (timeScalePathKernel c K) :=
  (ProbabilityMeasure.continuous_map (continuous_timeScalePath c)).comp hK

omit [MeasurableSpace E] [BorelSpace E] in
/-- A linear time change preserves the Markov property at the corresponding times. -/
theorem MarkovAt.timeScalePathKernel {K : E → ProbabilityMeasure C(ℝ≥0, E)}
    (hK : Continuous K) {z : E} (c t : ℝ≥0) (h : MarkovAt K z (c * t)) :
    MarkovAt (timeScalePathKernel c K) z t := by
  have h' := h.map_paths (continuous_timeScalePathKernel hK c)
    (timeScalePath c) (continuous_timeScalePath c) id
    (fun _ => rfl)
    (fun x => by
      refine ContinuousMap.ext fun u => ?_
      simp [stopPath_apply, mul_min_of_nonneg _ _ (zero_le : (0 : ℝ≥0) ≤ c)])
    (fun x => by
      refine ContinuousMap.ext fun u => ?_
      simp [pathShift_apply, mul_add])
    (fun _ => rfl)
  exact h'

end LatticeProb
