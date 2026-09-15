/-
The `p`-th power of a sum of two nonnegative reals, bounded by `2 ^ p` times the
sum of the `p`-th powers.  This is the convexity inequality behind the moment
bound for the supremum of a process over a box.
-/
import Mathlib

noncomputable section

namespace LatticeProb.RpowAdd

/-- `(x + y) ^ p ≤ 2 ^ p * (x ^ p + y ^ p)` for `x, y ≥ 0` and `p > 0`. -/
theorem add_rpow_le_two_rpow_mul {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 < p) :
    (x + y) ^ p ≤ (2 : ℝ) ^ p * (x ^ p + y ^ p) := by
  have hmax : x + y ≤ 2 * max x y := by
    have h1 := le_max_left x y
    have h2 := le_max_right x y
    linarith
  have h2 : (0 : ℝ) ≤ 2 * max x y := by
    have hx' : (0 : ℝ) ≤ max x y := le_max_of_le_left hx
    linarith
  calc (x + y) ^ p ≤ (2 * max x y) ^ p := Real.rpow_le_rpow (by positivity) hmax hp.le
    _ = (2 : ℝ) ^ p * (max x y) ^ p := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ (2 : ℝ) ^ p * (x ^ p + y ^ p) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) p)
        rcases le_total x y with h | h
        · rw [max_eq_right h]
          exact le_add_of_nonneg_left (Real.rpow_nonneg hx p)
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (Real.rpow_nonneg hy p)

end LatticeProb.RpowAdd
