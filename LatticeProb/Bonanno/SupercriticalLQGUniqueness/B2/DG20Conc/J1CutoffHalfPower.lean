/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffHalfPower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffIndexed

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_half_parameter_from_full (Q : LQGMetric.WhiteNoise.PsiParams)
    (K : ℕ) (T : ℝ)
    (hT : (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T) :
    (2 : ℝ)^(((1 / 2 : ℝ) *
      (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) < T^(1 / 2 : ℝ) := by
  have h := Real.rpow_lt_rpow (by positivity : 0 ≤
    (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) hT
    (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)] at h
  convert h using 1 <;> ring

theorem j1_half_cutoff_delta (ξ : ℝ) (hξ : 0 < ξ) :
    0 < (1 / (2 * ξ) : ℝ) ∧
      (1 / (2 * ξ) : ℝ) * |ξ| = 1 / 2 := by
  have h2 : 0 < 2 * ξ := by positivity
  constructor
  · positivity
  · rw [abs_of_pos hξ]
    field_simp

theorem j1_half_cutoff_low_threshold (T d : ℝ)
    (hT : 0 < T) :
    ENNReal.ofReal (T^(1 / 2 : ℝ)) * ENNReal.ofReal (T⁻¹ * d) =
      ENNReal.ofReal ((T^(1 / 2 : ℝ))⁻¹ * d) := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ T^(1 / 2 : ℝ))]
  congr 1
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hT]
  have hs : (1 / 2 : ℝ) + -1 = -(1 / 2) := by ring
  rw [hs, Real.rpow_neg hT.le]

theorem j1_half_cutoff_high_threshold (T d : ℝ)
    (hT : 0 < T) :
    ENNReal.ofReal (T^(1 / 2 : ℝ)) *
      ENNReal.ofReal (T^(1 / 2 : ℝ) * d) = ENNReal.ofReal (T * d) := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ T^(1 / 2 : ℝ))]
  congr 1
  rw [← mul_assoc, ← Real.rpow_add hT]
  norm_num

end SupercriticalLQGUniqueness.B2.DG20Conc
