import LatticeProb.Prob.BrownianOpenExit
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Monotone

/-!
# Ball exit times as functions of the radius

For every path, the first exit time from an open ball is nondecreasing in the radius,
Borel measurable, and continuous at almost every radius.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω E : Type*}

/-- Exit from a smaller set occurs no later than exit from a larger set. -/
theorem openExitTime_mono_set (B : ℝ≥0 → Ω → E) (ω : Ω) {U V : Set E}
    (hUV : U ⊆ V) : openExitTime B U ω ≤ openExitTime B V ω := by
  unfold openExitTime
  refine le_iInf fun t => ?_
  exact iInf_le (fun s : {s : ℝ≥0 // B s ω ∉ U} => (s.1 : ℝ≥0∞))
    ⟨t.1, fun ht => t.2 (hUV ht)⟩

variable [PseudoMetricSpace E]

/-- The first exit time from an open ball is nondecreasing in its radius. -/
theorem monotone_openExitTime_ball (B : ℝ≥0 → Ω → E) (ω : Ω) (x : E) :
    Monotone (fun r : ℝ => openExitTime B (Metric.ball x r) ω) :=
  fun _ _ h => openExitTime_mono_set B ω (Metric.ball_subset_ball h)

/-- The ball exit time is Borel measurable as a function of the radius. -/
theorem measurable_openExitTime_ball_radius (B : ℝ≥0 → Ω → E) (ω : Ω) (x : E) :
    Measurable (fun r : ℝ => openExitTime B (Metric.ball x r) ω) :=
  (monotone_openExitTime_ball B ω x).measurable

/-- The ball exit time is continuous in the radius outside a countable set. -/
theorem countable_not_continuousAt_openExitTime_ball_radius
    (B : ℝ≥0 → Ω → E) (ω : Ω) (x : E) :
    Set.Countable {r : ℝ | ¬ ContinuousAt (fun s : ℝ => openExitTime B (Metric.ball x s) ω) r} :=
  (monotone_openExitTime_ball B ω x).countable_not_continuousAt

/-- The ball exit time is continuous in the radius for almost every radius. -/
theorem ae_continuousAt_openExitTime_ball_radius (B : ℝ≥0 → Ω → E) (ω : Ω) (x : E) :
    ∀ᵐ r : ℝ ∂volume, ContinuousAt (fun s : ℝ => openExitTime B (Metric.ball x s) ω) r := by
  simpa only [ae_iff, not_not] using
    (countable_not_continuousAt_openExitTime_ball_radius B ω x).measure_zero volume

end LatticeProb
