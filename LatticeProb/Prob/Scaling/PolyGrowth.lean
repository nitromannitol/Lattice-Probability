/-
Generic real-number lemmas for propagating an explicit polynomial bound through a chain of
existentially-quantified constants that depend on a nonnegative parameter `A`: if a quantity is
already bounded by a FIXED, `A`-independent constant, or by an affine combination of such
constants together with a quantity already known to be `(1 + A) ^ e`-bounded, then the quantity
itself is bounded by `K * (1 + A) ^ e` for a SINGLE `A`-independent `K`.  Stated for abstract
real numbers only, so this module can move verbatim into the shared library.

Moved from Parking-Sharpness.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace LatticeProb.Scaling.PolyGrowth

/-- **`(1 + A) ^ e ≥ 1`** for `A ≥ 0`, `e ≥ 0`. -/
theorem one_le_one_add_rpow {A e : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e) : (1 : ℝ) ≤ (1 + A) ^ e := by
  have hA1 : (1 : ℝ) ≤ 1 + A := by linarith
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hA1 he
  rwa [Real.one_rpow] at h

/-- **A constant is trivially bounded by itself times `(1 + A) ^ e`**, since `(1 + A) ^ e ≥ 1`
for `A ≥ 0`, `e ≥ 0`. -/
theorem le_const_mul_one_add_rpow {x K A e : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (he : 0 ≤ e)
    (hx : x ≤ K) : x ≤ K * (1 + A) ^ e :=
  hx.trans (le_mul_of_one_le_right hK (one_le_one_add_rpow hA he))

/-- **The sum of an `A`-independent constant and an already-`(1 + A) ^ e`-bounded quantity is
`(1 + A) ^ e`-bounded, with the sum of the two constants.** -/
theorem le_add_const_mul_one_add_rpow {x K₁ K₂ A e : ℝ} (hK₂ : 0 ≤ K₂) (hA : 0 ≤ A) (he : 0 ≤ e)
    (hx : x ≤ K₁ * (1 + A) ^ e + K₂) : x ≤ (K₁ + K₂) * (1 + A) ^ e := by
  have h2 : K₂ ≤ K₂ * (1 + A) ^ e := le_const_mul_one_add_rpow hK₂ hA he le_rfl
  calc x ≤ K₁ * (1 + A) ^ e + K₂ := hx
    _ ≤ K₁ * (1 + A) ^ e + K₂ * (1 + A) ^ e := by linarith
    _ = (K₁ + K₂) * (1 + A) ^ e := by ring

/-- **A nonnegative scalar multiple of an already-`(1 + A) ^ e`-bounded quantity is
`(1 + A) ^ e`-bounded, with the scalar multiple of the constant.** -/
theorem le_const_mul_of_le_one_add_rpow {x K c A e : ℝ}
    (hx : x ≤ c * (K * (1 + A) ^ e)) : x ≤ (c * K) * (1 + A) ^ e := by
  rw [mul_assoc]; exact hx

end LatticeProb.Scaling.PolyGrowth

end
