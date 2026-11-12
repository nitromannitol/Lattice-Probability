/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20DSigma at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum

/-!
# DDDF Theorem 20, Step 4: the range of dependence at scales `[4^{-n}, 4^{-K}]` (task P2-DDDFT20d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1097 (`P^K` at distance `C K^{ε₀} 2^{-K}`): the range
`σ_t = r₀ √t (1 + |log t|)^{ε₀}` (`Def:sigma`) of the resampled field is at most
`r₀ (1+2ε₀)^{ε₀} (1 + K log 4)^{ε₀} 2^{-K}` for `t ≤ 4^{-K}` (`T20D.sigma_le_range`). Own elementary
proof: `t = 4^{-K} u`, `1 − log t ≤ (1 + K log 4)(1 − log u)` and `−log u ≤ 2ε₀ u^{-1/(2ε₀)}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DDDF
open WhiteNoise

namespace T20D

/-- **Range of dependence** (DDDF `Def:sigma`, l. 1097): `σ_t ≤ r₀ (1+2ε₀)^{ε₀} (1+K log 4)^{ε₀} 2^{-K}`
for `0 < t ≤ 4^{-K}` -/
theorem sigma_le_range (Q : PsiParams) (K : ℕ) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ ((2 : ℝ)⁻¹ ^ K) ^ 2) :
    Q.sigma t ≤ Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (1 + K * Real.log 4) ^ Q.ε₀ * (2 : ℝ)⁻¹ ^ K := by
  set h : ℝ := (2 : ℝ)⁻¹ ^ K with hh
  have hp : 0 < h := by positivity
  have hε := Q.ε₀_pos
  set u : ℝ := t / h ^ 2 with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one (by positivity)]; exact ht
  have ht' : t = h ^ 2 * u := by rw [hu]; field_simp
  have hlogh : Real.log (h ^ 2) = -(K * Real.log 4) := by
    rw [hh, ← pow_mul, Real.log_pow, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast; ring
  have hlogt : |Real.log t| = K * Real.log 4 + (-Real.log u) := by
    have hneg : Real.log t ≤ 0 := Real.log_nonpos ht0.le (ht.trans (by
      rw [hh]; exact pow_le_one₀ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))))
    rw [abs_of_nonpos hneg, ht', Real.log_mul (by positivity) hu0.ne', hlogh]; ring
  have hlu : 0 ≤ -Real.log u := by linarith [Real.log_nonpos hu0.le hu1]
  have hK4 : 0 ≤ (K : ℝ) * Real.log 4 := by positivity
  set δ : ℝ := 1 / (2 * Q.ε₀)
  have hδ : 0 < δ := by positivity
  have hv1 : 1 ≤ u⁻¹ := one_le_inv_iff₀.2 ⟨hu0, hu1⟩
  have hpow1 : 1 ≤ u⁻¹ ^ δ := Real.one_le_rpow hv1 hδ.le
  have hlog : -Real.log u ≤ u⁻¹ ^ δ / δ := by
    rw [← Real.log_inv]; exact Real.log_le_rpow_div (by positivity) hδ
  have h1δ : 1 / δ = 2 * Q.ε₀ := by simp only [δ]; field_simp
  have hA : 1 + |Real.log t| ≤ (1 + K * Real.log 4) * ((1 + 2 * Q.ε₀) * u⁻¹ ^ δ) := by
    rw [hlogt]
    have h2 : 1 + -Real.log u ≤ (1 + 2 * Q.ε₀) * u⁻¹ ^ δ := by
      have : u⁻¹ ^ δ / δ = 2 * Q.ε₀ * u⁻¹ ^ δ := by rw [div_eq_mul_one_div, h1δ]; ring
      nlinarith
    nlinarith
  have hB : (1 + |Real.log t|) ^ Q.ε₀ ≤
      (1 + K * Real.log 4) ^ Q.ε₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (u⁻¹ ^ δ) ^ Q.ε₀ := by
    refine (Real.rpow_le_rpow (by positivity) hA hε.le).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    ring
  have hC : (u⁻¹ ^ δ) ^ Q.ε₀ * Real.sqrt u = 1 := by
    rw [← Real.rpow_mul (by positivity), show δ * Q.ε₀ = 1 / 2 by simp only [δ]; field_simp,
      Real.sqrt_eq_rpow, Real.inv_rpow hu0.le, inv_mul_cancel₀ (by positivity)]
  have hsq : Real.sqrt t = h * Real.sqrt u := by
    rw [ht', Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]
  unfold PsiParams.sigma
  rw [hsq]
  have hr := Q.r₀_pos
  calc Q.r₀ * (h * Real.sqrt u) * (1 + |Real.log t|) ^ Q.ε₀
      ≤ Q.r₀ * (h * Real.sqrt u) *
        ((1 + K * Real.log 4) ^ Q.ε₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (u⁻¹ ^ δ) ^ Q.ε₀) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (1 + K * Real.log 4) ^ Q.ε₀ * h *
        ((u⁻¹ ^ δ) ^ Q.ε₀ * Real.sqrt u) := by ring
    _ = _ := by rw [hC, mul_one]

end T20D
end DDDF
end LQGMetric
