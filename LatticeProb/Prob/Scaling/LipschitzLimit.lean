/-
**A pointwise limit of uniformly `1`-Lipschitz functions is itself `1`-Lipschitz.**

Given a family `fR : ℝ → E → ℝ` of uniformly `1`-Lipschitz functions converging pointwise to a
function `f : E → ℝ`, `f` is itself `1`-Lipschitz and, whenever `E` carries a Borel measurable
structure, measurable. This is free from the Lipschitz bound and the pointwise limit alone:
`|f y - f x| = lim_R |fR R y - fR R x| ≤ dist y x` since each term of the sequence is bounded by
`dist y x`, with no further analytic content about the particular family `fR` needed.

Moved from Parking-Sharpness.
-/
import Mathlib

open Filter Topology

noncomputable section

namespace LatticeProb.Scaling.LipschitzLimit

variable {E : Type*} [PseudoMetricSpace E]

/-- **The pointwise limit, along `atTop` on `ℝ`, of functions that are uniformly `1`-Lipschitz
is itself `1`-Lipschitz.** -/
theorem lipschitzWith_one_of_tendsto (fR : ℝ → E → ℝ) (f : E → ℝ)
    (hLip : ∀ (R : ℝ) (y x : E), |fR R y - fR R x| ≤ dist y x)
    (hpt : ∀ x : E, Tendsto (fun R => fR R x) atTop (𝓝 (f x))) :
    LipschitzWith 1 f := by
  refine LipschitzWith.of_dist_le_mul fun y x => ?_
  rw [NNReal.coe_one, one_mul]
  have hsub : Tendsto (fun R => fR R y - fR R x) atTop (𝓝 (f y - f x)) :=
    (hpt y).sub (hpt x)
  have habs : Tendsto (fun R => |fR R y - fR R x|) atTop (𝓝 (|f y - f x|)) := hsub.abs
  have hle : |f y - f x| ≤ dist y x :=
    le_of_tendsto habs (Filter.Eventually.of_forall fun R => hLip R y x)
  rwa [Real.dist_eq]

/-- **Consequently, the pointwise limit is measurable.** -/
theorem measurable_of_tendsto [MeasurableSpace E] [OpensMeasurableSpace E]
    (fR : ℝ → E → ℝ) (f : E → ℝ)
    (hLip : ∀ (R : ℝ) (y x : E), |fR R y - fR R x| ≤ dist y x)
    (hpt : ∀ x : E, Tendsto (fun R => fR R x) atTop (𝓝 (f x))) :
    Measurable f :=
  (lipschitzWith_one_of_tendsto fR f hLip hpt).continuous.measurable

end LatticeProb.Scaling.LipschitzLimit

end
