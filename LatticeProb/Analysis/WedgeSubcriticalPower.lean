import LatticeProb.Analysis.WedgeHarmonicPower

/-! # Subcritical power profiles on a wedge -/

set_option autoImplicit false

namespace LatticeProb

/-- A subcritical power profile has a positive radial lower bound throughout
the closed angular sector, including its two boundary rays. -/
theorem wedge_re_cpow_lower_bound_subcritical {θ p r : ℝ}
    (hθ : 0 < θ) (hp : 0 < p) (hpθ : p * θ < Real.pi)
    (hr : 0 ≤ r) {z : ℂ} (hz : z ≠ 0) (hrz : r ≤ ‖z‖)
    (ha : |z.arg| ≤ θ / 2) :
    Real.cos (p * (θ / 2)) * r ^ p ≤ (z ^ (p : ℂ)).re := by
  have hangle : 0 ≤ p * (θ / 2) := mul_nonneg hp.le (by linarith)
  have hangleπ : p * (θ / 2) < Real.pi / 2 := by nlinarith
  have hc : 0 < Real.cos (p * (θ / 2)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, hangleπ⟩
  have hcos : Real.cos (p * (θ / 2)) ≤ Real.cos (p * z.arg) := by
    rw [← Real.cos_abs (p * z.arg)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left ha hp.le
  have hrpow : r ^ p ≤ ‖z‖ ^ p := Real.rpow_le_rpow hr hrz hp.le
  rw [re_cpow_eq_rpow_mul_cos_arg hz]
  calc
    Real.cos (p * (θ / 2)) * r ^ p ≤ Real.cos (p * (θ / 2)) * ‖z‖ ^ p :=
      mul_le_mul_of_nonneg_left hrpow hc.le
    _ ≤ ‖z‖ ^ p * Real.cos (p * z.arg) := by
      rw [mul_comm (Real.cos (p * (θ / 2)))]
      exact mul_le_mul_of_nonneg_left hcos (Real.rpow_nonneg (norm_nonneg _) _)

end LatticeProb
