/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScale at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLargeKScale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DSigma

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneC_sigma_le_quarter_source_scale
    (Q : PsiParams) (hR : Q.r₀ ≤ (1 : ℝ) / 100)
    (hε : Q.ε₀ ≤ (1 : ℝ) / 100)
    {K : ℕ} (hK : 1 ≤ K) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ (((2 : ℝ)⁻¹ ^ K) ^ 2)) :
    Q.sigma t ≤ ((K : ℝ) ^ Q.ε₀ / 4) * (2 : ℝ)⁻¹ ^ K := by
  have hε0 := Q.ε₀_pos
  have hε1 : Q.ε₀ ≤ 1 := by linarith
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
  have hA0 : 1 + 2 * Q.ε₀ ≤ 2 := by linarith
  have hA : (1 + 2 * Q.ε₀) ^ Q.ε₀ ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ Q.ε₀ :=
        Real.rpow_le_rpow (by positivity) hA0 hε0.le
      _ ≤ 2 := by
        convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hε1
          using 1 <;> norm_num
  have hB0 : 1 + K * Real.log 4 ≤ 4 * (K : ℝ) := by nlinarith
  have h4 : (4 : ℝ) ^ Q.ε₀ ≤ 4 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hε1
      using 1 <;> norm_num
  have hKpow : 0 ≤ (K : ℝ) ^ Q.ε₀ := Real.rpow_nonneg (by positivity) _
  have hB : (1 + K * Real.log 4) ^ Q.ε₀ ≤
      4 * (K : ℝ) ^ Q.ε₀ := by
    calc
      _ ≤ (4 * (K : ℝ)) ^ Q.ε₀ :=
        Real.rpow_le_rpow (by positivity) hB0 hε0.le
      _ = (4 : ℝ) ^ Q.ε₀ * (K : ℝ) ^ Q.ε₀ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity)]
      _ ≤ 4 * (K : ℝ) ^ Q.ε₀ :=
        mul_le_mul_of_nonneg_right h4 hKpow
  have hR0 : 0 ≤ Q.r₀ := Q.r₀_pos.le
  have hApos : 0 ≤ (1 + 2 * Q.ε₀) ^ Q.ε₀ := by positivity
  have hBpos : 0 ≤ (1 + K * Real.log 4) ^ Q.ε₀ := by positivity
  have hcoef : Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ *
      (1 + K * Real.log 4) ^ Q.ε₀ ≤ (K : ℝ) ^ Q.ε₀ / 4 := by
    calc
      _ ≤ ((1 : ℝ) / 100) * (1 + 2 * Q.ε₀) ^ Q.ε₀ *
          (1 + K * Real.log 4) ^ Q.ε₀ := by
            apply mul_le_mul_of_nonneg_right _ hBpos
            exact mul_le_mul_of_nonneg_right hR hApos
      _ ≤ ((1 : ℝ) / 100) * 2 *
          (1 + K * Real.log 4) ^ Q.ε₀ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hA (by norm_num)) hBpos
      _ ≤ ((1 : ℝ) / 100) * 2 * (4 * (K : ℝ) ^ Q.ε₀) := by
            exact mul_le_mul_of_nonneg_left hB (by norm_num)
      _ ≤ (K : ℝ) ^ Q.ε₀ / 4 := by nlinarith
  exact (T20D.sigma_le_range Q K ht0 ht).trans
    (mul_le_mul_of_nonneg_right hcoef (by positivity))

 

end SupercriticalLQGUniqueness.B2.DG20Conc
