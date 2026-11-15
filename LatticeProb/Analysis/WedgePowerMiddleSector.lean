import LatticeProb.Analysis.WedgeHarmonicPower

/-! # A lower bound for the power profile in an interior sector -/

set_option autoImplicit false

namespace LatticeProb

/-- On the middle half of a symmetric wedge, the positive power profile is
bounded below by a fixed positive multiple of the corresponding radial power. -/
theorem wedge_re_cpow_lower_bound_middle_sector {θ r : ℝ} (hθ : 0 < θ)
    (hr : 0 ≤ r) {z : ℂ} (hz : z ≠ 0) (hrz : r ≤ ‖z‖)
    (ha : |z.arg| ≤ θ / 4) :
    (Real.sqrt 2 / 2) * r ^ (Real.pi / θ) ≤
      (z ^ ((Real.pi / θ : ℝ) : ℂ)).re := by
  have hp : 0 < Real.pi / θ := div_pos Real.pi_pos hθ
  have hpangle : |(Real.pi / θ) * z.arg| ≤ Real.pi / 4 := by
    rw [abs_mul, abs_of_pos hp]
    calc
      (Real.pi / θ) * |z.arg| ≤ (Real.pi / θ) * (θ / 4) :=
        mul_le_mul_of_nonneg_left ha hp.le
      _ = Real.pi / 4 := by field_simp
  have hc : Real.sqrt 2 / 2 ≤ Real.cos ((Real.pi / θ) * z.arg) := by
    rw [← Real.cos_pi_div_four, ← Real.cos_abs ((Real.pi / θ) * z.arg)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hpangle
  have hrpow : r ^ (Real.pi / θ) ≤ ‖z‖ ^ (Real.pi / θ) :=
    Real.rpow_le_rpow hr hrz hp.le
  rw [re_cpow_eq_rpow_mul_cos_arg hz]
  calc
    (Real.sqrt 2 / 2) * r ^ (Real.pi / θ) ≤
        (Real.sqrt 2 / 2) * ‖z‖ ^ (Real.pi / θ) :=
      mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ ≤ ‖z‖ ^ (Real.pi / θ) * Real.cos ((Real.pi / θ) * z.arg) := by
      rw [mul_comm (Real.sqrt 2 / 2)]
      exact mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (norm_nonneg _) _)

end LatticeProb
