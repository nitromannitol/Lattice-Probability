/-
A one-line arithmetic fact about `min`: the product of two minima lower-bounds the minimum of
the cross products, for nonnegative reals. Stated for four arbitrary nonnegative reals; useful
for collapsing two independently-obtained rate constants (for instance two dimension-dependent
kernel-norm bounds) into a single rate constant for their product.

Moved from Parking-Sharpness.
-/
import Mathlib

noncomputable section
namespace LatticeProb.Scaling.MinProduct

/-- **The product of two minima lower-bounds the minimum of the cross products.**  For
nonnegative reals `a, b, x, y`: `min a b * min x y ≤ min (a * x) (b * y)`.  Proof: `min a b ≤ a`
and `min x y ≤ x` combine (both nonnegative) to `min a b * min x y ≤ a * x`, and symmetrically
for `b * y`; take the `min` of both. -/
theorem min_mul_min_le (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min a b * min x y ≤ min (a * x) (b * y) := by
  refine le_min ?_ ?_
  · exact mul_le_mul (min_le_left a b) (min_le_left x y) (le_min hx hy) ha
  · exact mul_le_mul (min_le_right a b) (min_le_right x y) (le_min hx hy) hb

end LatticeProb.Scaling.MinProduct
end
