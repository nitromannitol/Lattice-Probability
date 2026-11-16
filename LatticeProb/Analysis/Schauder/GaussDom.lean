import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Pointwise Gaussian dominations

Elementary pointwise bounds that absorb a polynomial factor into half of a Gaussian: for `b > 0`,
`|s| exp(-b s²) ≤ b^{-1/2} exp(-(b/2) s²)` and `s² exp(-b s²) ≤ b⁻¹ exp(-(b/2) s²)`, together with
their versions for the norm on an arbitrary normed group.

They reduce every derivative bound for the heat kernel to the Gaussian integral
`∫ exp(-b‖x‖²) = (π/b)^{d/2}`, after the polynomial prefactor produced by differentiating the
kernel has been dominated by a power of `b⁻¹` times a Gaussian of half the strength.
-/

namespace LatticeProb.Analysis.Schauder

open Real

noncomputable section

/-- For `y ≥ 0` the elementary bound `y ≤ exp(y/2)`. -/
private theorem le_exp_half {y : ℝ} (hy : 0 ≤ y) : y ≤ Real.exp (y / 2) := by
  have h1 : y / 4 + 1 ≤ Real.exp (y / 4) := Real.add_one_le_exp (y / 4)
  have h2 : Real.exp (y / 2) = Real.exp (y / 4) * Real.exp (y / 4) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : (y / 4 + 1) * (y / 4 + 1) ≤ Real.exp (y / 4) * Real.exp (y / 4) :=
    mul_self_le_mul_self (by linarith) h1
  rw [h2]
  nlinarith [sq_nonneg (1 - y / 4)]

/-- The Gaussian factor `exp(-y/2)` is the inverse of `exp(y/2)`. -/
private theorem exp_neg_half_eq_inv (y : ℝ) : Real.exp (-y / 2) = (Real.exp (y / 2))⁻¹ := by
  rw [neg_div, Real.exp_neg]

/-- A linear factor is absorbed by half a Gaussian: `y exp(-y/2) ≤ 1` for `y ≥ 0`. -/
theorem mul_exp_neg_half_le_one {y : ℝ} (hy : 0 ≤ y) : y * Real.exp (-y / 2) ≤ 1 := by
  rw [exp_neg_half_eq_inv, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact le_exp_half hy

/-- A square-root factor is absorbed by half a Gaussian: `√y exp(-y/2) ≤ 1` for `y ≥ 0`. -/
theorem sqrt_mul_exp_neg_half_le_one {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt y * Real.exp (-y / 2) ≤ 1 := by
  rw [exp_neg_half_eq_inv, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  have h1 : Real.sqrt y ≤ 1 + y / 2 := by
    nlinarith [sq_nonneg (Real.sqrt y - 1), Real.sq_sqrt hy]
  have h2 : y / 2 + 1 ≤ Real.exp (y / 2) := Real.add_one_le_exp (y / 2)
  linarith

/-- The factor `|s|` is absorbed by half of the Gaussian `exp(-b s²)`, at the price `b^{-1/2}`. -/
theorem abs_mul_exp_neg_le {b : ℝ} (hb : 0 < b) (s : ℝ) :
    |s| * Real.exp (-b * s ^ 2) ≤ (Real.sqrt b)⁻¹ * Real.exp (-(b / 2) * s ^ 2) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hy : 0 ≤ b * s ^ 2 := by positivity
  have h1 : |s| = (Real.sqrt b)⁻¹ * Real.sqrt (b * s ^ 2) := by
    rw [Real.sqrt_mul hb.le, Real.sqrt_sq_eq_abs]
    field_simp
  have h2 : Real.exp (-b * s ^ 2) = Real.exp (-(b * s ^ 2) / 2) * Real.exp (-(b / 2) * s ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have h3 := sqrt_mul_exp_neg_half_le_one hy
  have h4 : 0 ≤ Real.exp (-(b / 2) * s ^ 2) := (Real.exp_pos _).le
  rw [h1, h2]
  calc (Real.sqrt b)⁻¹ * Real.sqrt (b * s ^ 2) *
        (Real.exp (-(b * s ^ 2) / 2) * Real.exp (-(b / 2) * s ^ 2))
      = (Real.sqrt b)⁻¹ * (Real.sqrt (b * s ^ 2) * Real.exp (-(b * s ^ 2) / 2)) *
        Real.exp (-(b / 2) * s ^ 2) := by ring
    _ ≤ (Real.sqrt b)⁻¹ * 1 * Real.exp (-(b / 2) * s ^ 2) := by
        gcongr
    _ = (Real.sqrt b)⁻¹ * Real.exp (-(b / 2) * s ^ 2) := by ring

/-- The factor `s²` is absorbed by half of the Gaussian `exp(-b s²)`, at the price `b⁻¹`. -/
theorem sq_mul_exp_neg_le {b : ℝ} (hb : 0 < b) (s : ℝ) :
    s ^ 2 * Real.exp (-b * s ^ 2) ≤ b⁻¹ * Real.exp (-(b / 2) * s ^ 2) := by
  have hy : 0 ≤ b * s ^ 2 := by positivity
  have hb' : b⁻¹ * b = 1 := inv_mul_cancel₀ hb.ne'
  have h2 : Real.exp (-b * s ^ 2) = Real.exp (-(b * s ^ 2) / 2) * Real.exp (-(b / 2) * s ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have h3 := mul_exp_neg_half_le_one hy
  have h4 : 0 ≤ Real.exp (-(b / 2) * s ^ 2) := (Real.exp_pos _).le
  have h5 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  rw [h2]
  calc s ^ 2 * (Real.exp (-(b * s ^ 2) / 2) * Real.exp (-(b / 2) * s ^ 2))
      = b⁻¹ * ((b * s ^ 2) * Real.exp (-(b * s ^ 2) / 2)) * Real.exp (-(b / 2) * s ^ 2) := by
        linear_combination
          (-(s ^ 2 * Real.exp (-(b * s ^ 2) / 2) * Real.exp (-(b / 2) * s ^ 2))) * hb'
    _ ≤ b⁻¹ * 1 * Real.exp (-(b / 2) * s ^ 2) := by
        gcongr
    _ = b⁻¹ * Real.exp (-(b / 2) * s ^ 2) := by ring

/-- The norm version of `abs_mul_exp_neg_le`. -/
theorem norm_mul_exp_neg_le {E : Type*} [NormedAddCommGroup E] {b : ℝ} (hb : 0 < b) (x : E) :
    ‖x‖ * Real.exp (-b * ‖x‖ ^ 2) ≤ (Real.sqrt b)⁻¹ * Real.exp (-(b / 2) * ‖x‖ ^ 2) := by
  simpa [abs_norm] using abs_mul_exp_neg_le hb ‖x‖

/-- The norm version of `sq_mul_exp_neg_le`. -/
theorem norm_sq_mul_exp_neg_le {E : Type*} [NormedAddCommGroup E] {b : ℝ} (hb : 0 < b) (x : E) :
    ‖x‖ ^ 2 * Real.exp (-b * ‖x‖ ^ 2) ≤ b⁻¹ * Real.exp (-(b / 2) * ‖x‖ ^ 2) :=
  sq_mul_exp_neg_le hb ‖x‖

end

end LatticeProb.Analysis.Schauder
