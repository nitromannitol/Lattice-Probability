/-
The homogeneity of `sSup` under a nonnegative scalar, for the set of values an abstract
optimal-stopping problem's admissible rules produce.  Stated for an arbitrary `Set ℝ` (the
image of the set of values under multiplication by the reward's scale is the scale times the
supremum), so this module can move verbatim into the shared library.  The scaling of the value
of a terminal-reward stopping problem, `sSup ((c * F) '' rules) = c * sSup (F '' rules)`, is an
instance of this with `S` the set of terminal values.

Moved from Parking-Sharpness.
-/
import Mathlib.Data.Real.Pointwise
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set

open scoped Pointwise

noncomputable section

namespace LatticeProb.Scaling.OptimalStopping

/-- **A set bounded above stays bounded above after scaling by a nonnegative constant.** -/
theorem bddAbove_const_mul_image_of_nonneg {S : Set ℝ} (hS : BddAbove S) {c : ℝ} (hc : 0 ≤ c) :
    BddAbove ((fun a => c * a) '' S) := by
  obtain ⟨M, hM⟩ := hS
  exact ⟨c * M, by rintro a ⟨s, hs, rfl⟩; exact mul_le_mul_of_nonneg_left (hM hs) hc⟩

/-- **`sSup` is homogeneous of degree `1` under a nonnegative scalar**: the supremum of the
image of a set under multiplication by `c ≥ 0` is `c` times the original supremum, for EVERY
set (empty, unbounded, or otherwise — no side condition needed). -/
theorem sSup_const_mul_image_of_nonneg (S : Set ℝ) {c : ℝ} (hc : 0 ≤ c) :
    sSup ((fun a => c * a) '' S) = c * sSup S := by
  have himg : (fun a => c * a) '' S = c • S := rfl
  rw [himg, Real.sSup_smul_of_nonneg hc]
  rfl

end LatticeProb.Scaling.OptimalStopping

end
