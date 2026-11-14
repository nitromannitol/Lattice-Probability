import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-!
# Uniform continuity and linear interpolation

On short segments, a uniformly continuous map nearly commutes with linear
interpolation, provided the segment point lies in the set of uniform continuity.
-/

namespace LatticeProb

open AffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The two ways of interpolating the image of a short segment are uniformly close. -/
theorem UniformContinuousOn.dist_image_lineMap_lt {K : Set E} {f : E → F}
    (hf : UniformContinuousOn f K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      lineMap x y t ∈ K → dist x y < δ →
      dist (f (lineMap x y t)) (lineMap (f x) (f y) t) < ε := by
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hf) (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy t ht hz hxy
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have ht_norm : ‖t‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg ht0] using ht1
  have hzx : dist (lineMap x y t) x < δ := by
    rw [dist_lineMap_left]
    calc
      ‖t‖ * dist x y ≤ 1 * dist x y := mul_le_mul_of_nonneg_right ht_norm dist_nonneg
      _ < δ := by simpa using hxy
  have h1 := hmod (lineMap x y t) hz x hx hzx
  have h2 := hmod x hx y hy hxy
  have h3 : dist (f x) (lineMap (f x) (f y) t) ≤ dist (f x) (f y) := by
    rw [dist_left_lineMap]
    simpa using mul_le_mul_of_nonneg_right ht_norm (dist_nonneg : 0 ≤ dist (f x) (f y))
  have htriangle := dist_triangle (f (lineMap x y t)) (f x) (lineMap (f x) (f y) t)
  linarith

end LatticeProb
