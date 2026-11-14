/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.GaussianTwoSum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.OneBoxLowerTail

 

set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 
theorem gaussian_two_sum_bound
    (a₀ a₁ b₀ b₁ T : ℝ) (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) :
    ENNReal.ofReal (a₀ * Real.exp (-b₀ * (Real.log T) ^ 2)) +
      ENNReal.ofReal (a₁ * Real.exp (-b₁ * (Real.log T) ^ 2)) ≤
    ENNReal.ofReal ((a₀ + a₁) * Real.exp (-(min b₀ b₁) * (Real.log T) ^ 2)) := by
  have hterm (a b : ℝ) (ha : 0 < a) (hb : min b₀ b₁ ≤ b) :
      a * Real.exp (-b * (Real.log T) ^ 2) ≤
        a * Real.exp (-(min b₀ b₁) * (Real.log T) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ ha.le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg (Real.log T))]
  have hsum :
      a₀ * Real.exp (-b₀ * (Real.log T) ^ 2) +
      a₁ * Real.exp (-b₁ * (Real.log T) ^ 2) ≤
      (a₀ + a₁) * Real.exp (-(min b₀ b₁) * (Real.log T) ^ 2) := by
    nlinarith [add_le_add
      (hterm a₀ b₀ ha₀ (min_le_left _ _))
      (hterm a₁ b₁ ha₁ (min_le_right _ _))]
  rw [← ENNReal.ofReal_add
    (by positivity : 0 ≤ a₀ * Real.exp (-b₀ * (Real.log T) ^ 2))
    (by positivity : 0 ≤ a₁ * Real.exp (-b₁ * (Real.log T) ^ 2))]
  exact ENNReal.ofReal_le_ofReal hsum

end SupercriticalLQGUniqueness.B2.DG20Pt

