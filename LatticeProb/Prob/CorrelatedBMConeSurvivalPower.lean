import LatticeProb.Prob.CorrelatedBMConeUniformSurvival

/-! # Power estimates for separated cone grid events -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Convert a joint-window power estimate into the corresponding grid-event power. -/
theorem cone_survival_power_bound (C x h g B p : ℝ) (J : ℝ≥0∞)
    (hC : 0 < C) (hx : 0 < x) (hh : 0 < h) (hB : 0 ≤ B)
    (hJ : J ≤ ENNReal.ofReal (B * (C * x) ^ p)) :
    (ENNReal.ofReal (3 * (C * x) / √h) * J +
      ENNReal.ofReal (3 * (C * x) / √h) * J) *
      ENNReal.ofReal (2 * (C * x) / √g) ≤
    ENNReal.ofReal ((12 * B * C ^ (p + 2) / (√h * √g)) * x ^ (p + 2)) := by
  have hq : 0 < C * x := mul_pos hC hx
  have ha : 0 ≤ 3 * (C * x) / √h := by positivity
  have hb : 0 ≤ B * (C * x) ^ p := mul_nonneg hB (Real.rpow_nonneg hq.le _)
  calc
    _ ≤ (ENNReal.ofReal (3 * (C * x) / √h) * ENNReal.ofReal (B * (C * x) ^ p) +
        ENNReal.ofReal (3 * (C * x) / √h) * ENNReal.ofReal (B * (C * x) ^ p)) *
        ENNReal.ofReal (2 * (C * x) / √g) := by gcongr
    _ = ENNReal.ofReal (((3 * (C * x) / √h) * (B * (C * x) ^ p) +
        (3 * (C * x) / √h) * (B * (C * x) ^ p)) * (2 * (C * x) / √g)) := by
      rw [ENNReal.ofReal_mul (add_nonneg (mul_nonneg ha hb) (mul_nonneg ha hb)),
        ENNReal.ofReal_add (mul_nonneg ha hb) (mul_nonneg ha hb), ENNReal.ofReal_mul ha]
    _ = _ := by
      congr 1
      rw [Real.mul_rpow hC.le hx.le, Real.rpow_add hC p 2,
        Real.rpow_add hx p 2, Real.rpow_two, Real.rpow_two]
      ring

end LatticeProb.CorrelatedBM
