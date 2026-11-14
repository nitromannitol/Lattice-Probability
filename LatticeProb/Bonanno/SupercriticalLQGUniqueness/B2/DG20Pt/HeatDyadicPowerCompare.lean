/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatDyadicPowerCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_dyadic_power_compare
    (k : ℕ) (s₁ s₂ a t : ℝ)
    (hs₁ : 0 ≤ s₁) (hs₁' : s₁ ≤ 1)
    (hs₂ : 0 ≤ s₂) (hs₂' : s₂ ≤ 1)
    (ht : t = (2 : ℝ) ^ (-((k : ℝ) + s₁ - s₂))) :
    (2 : ℝ) ^ (-|a|) * t ^ a ≤
        (2 : ℝ) ^ (-a * (k : ℝ)) ∧
      (2 : ℝ) ^ (-a * (k : ℝ)) ≤
        (2 : ℝ) ^ |a| * t ^ a := by
  have hs : |s₁ - s₂| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hdiff : |a * (s₁ - s₂)| ≤ |a| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hs (abs_nonneg a)).trans_eq (mul_one _)
  have hlo : (2 : ℝ) ^ (-|a|) ≤ (2 : ℝ) ^ (a * (s₁ - s₂)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [abs_le.mp hdiff])
  have hhi : (2 : ℝ) ^ (a * (s₁ - s₂)) ≤ (2 : ℝ) ^ |a| :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      ((le_abs_self _).trans hdiff)
  have heq : (2 : ℝ) ^ (-a * (k : ℝ)) =
      t ^ a * (2 : ℝ) ^ (a * (s₁ - s₂)) := by
    rw [ht, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  rw [heq]
  constructor
  · simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hlo (Real.rpow_nonneg ht0 _)
  · simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hhi (Real.rpow_nonneg ht0 _)

end SupercriticalLQGUniqueness.B2.DG20Pt
