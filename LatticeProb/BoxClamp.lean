/- Adapted from nitromannitol/Parking-Sharpness, Apache-2.0. -/
/-
Extending a continuous function on a compact rectangle `[0,T] × [-2A,2A]` to the whole plane
by clamping the argument to the rectangle, for an arbitrary `T, A ≥ 0`.  Stated for abstract
reals.  The extension is bounded by the norm of the original function and is an isometry for
the supremum norm: this is the reading that turns a stopping value or a field value (a
functional of a REWARD FIELD restricted to a compact spatial-time box) into a Lipschitz
functional of a point of `C(rewardBox T A, ℝ)`, which is exactly what the extended continuous
mapping theorem needs.
-/
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

noncomputable section

namespace LatticeProb.BoxClamp

/-- The compact rectangle `[0,T] × [-2A, 2A]`. -/
abbrev rewardBox (T A : ℝ) : Type :=
  ↥(Set.Icc (0 : ℝ) T) × ↥(Set.Icc (-(2 * A)) (2 * A))

/-- The box is nonempty in its space coordinate. -/
theorem neg_two_mul_le_two_mul {A : ℝ} (hA : 0 ≤ A) : -(2 * A) ≤ 2 * A := by linarith

/-- The point of the box that a point of the plane is clamped to. -/
def boxPoint {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (s y : ℝ) : rewardBox T A :=
  (Set.projIcc (0 : ℝ) T hT s, Set.projIcc (-(2 * A)) (2 * A) (neg_two_mul_le_two_mul hA) y)

/-- A continuous reward on the box, extended to the whole of `ℝ × ℝ` by
clamping the argument to the box. -/
def rewardOfBox {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (G : C(rewardBox T A, ℝ)) :
    ℝ → ℝ → ℝ :=
  fun s y => G (boxPoint hT hA s y)

/-- **The extension is continuous on the plane.** -/
theorem continuous_rewardOfBox {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G : C(rewardBox T A, ℝ)) :
    Continuous (fun p : ℝ × ℝ => rewardOfBox hT hA G p.1 p.2) :=
  G.continuous.comp
    (((continuous_projIcc).comp continuous_fst).prodMk
      ((continuous_projIcc).comp continuous_snd))

/-- **The extension is bounded by the norm of the reward.** -/
theorem abs_rewardOfBox_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G : C(rewardBox T A, ℝ)) (s y : ℝ) : |rewardOfBox hT hA G s y| ≤ ‖G‖ := by
  show |G (boxPoint hT hA s y)| ≤ ‖G‖
  simpa [Real.norm_eq_abs] using G.norm_coe_le_norm (boxPoint hT hA s y)

/-- **The extension is an isometry for the supremum norm**: the extensions of
two rewards differ by at most their distance in `C(K)`. -/
theorem abs_rewardOfBox_sub_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G H : C(rewardBox T A, ℝ)) (s y : ℝ) :
    |rewardOfBox hT hA G s y - rewardOfBox hT hA H s y| ≤ dist G H := by
  show |G (boxPoint hT hA s y) - H (boxPoint hT hA s y)| ≤ dist G H
  simpa [Real.dist_eq] using
    (ContinuousMap.dist_apply_le_dist (f := G) (g := H) (boxPoint hT hA s y))

end LatticeProb.BoxClamp

end
