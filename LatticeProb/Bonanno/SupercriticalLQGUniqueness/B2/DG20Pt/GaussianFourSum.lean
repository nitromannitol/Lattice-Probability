/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.GaussianFourSum at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.MinFourTail

 




set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem gaussian_four_sum_bound
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ T : ℝ)
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) :
    ENNReal.ofReal (a₀ * Real.exp (-b₀ * (Real.log T) ^ 2)) +
      ENNReal.ofReal (a₁ * Real.exp (-b₁ * (Real.log T) ^ 2)) +
      ENNReal.ofReal (a₂ * Real.exp (-b₂ * (Real.log T) ^ 2)) +
      ENNReal.ofReal (a₃ * Real.exp (-b₃ * (Real.log T) ^ 2)) ≤
    ENNReal.ofReal ((a₀ + a₁ + a₂ + a₃) * Real.exp
      (-(min (min b₀ b₁) (min b₂ b₃)) * (Real.log T) ^ 2)) := by
  let b : ℝ := min (min b₀ b₁) (min b₂ b₃)
  have hbi₀ : b ≤ b₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hbi₁ : b ≤ b₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hbi₂ : b ≤ b₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hbi₃ : b ≤ b₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hterm (aᵢ bᵢ : ℝ) (haᵢ : 0 < aᵢ) (hbi : b ≤ bᵢ) :
      aᵢ * Real.exp (-bᵢ * (Real.log T) ^ 2) ≤
        aᵢ * Real.exp (-b * (Real.log T) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ haᵢ.le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hbi) (sq_nonneg (Real.log T))]
  have hsum :
      a₀ * Real.exp (-b₀ * (Real.log T) ^ 2) +
      a₁ * Real.exp (-b₁ * (Real.log T) ^ 2) +
      a₂ * Real.exp (-b₂ * (Real.log T) ^ 2) +
      a₃ * Real.exp (-b₃ * (Real.log T) ^ 2) ≤
      (a₀ + a₁ + a₂ + a₃) * Real.exp (-b * (Real.log T) ^ 2) := by
    have h := add_le_add
      (add_le_add (hterm a₀ b₀ ha₀ hbi₀) (hterm a₁ b₁ ha₁ hbi₁))
      (add_le_add (hterm a₂ b₂ ha₂ hbi₂) (hterm a₃ b₃ ha₃ hbi₃))
    nlinarith [h]
  have hnonneg₀ : 0 ≤ a₀ * Real.exp (-b₀ * (Real.log T) ^ 2) := by positivity
  have hnonneg₁ : 0 ≤ a₁ * Real.exp (-b₁ * (Real.log T) ^ 2) := by positivity
  have hnonneg₂ : 0 ≤ a₂ * Real.exp (-b₂ * (Real.log T) ^ 2) := by positivity
  have hnonneg₃ : 0 ≤ a₃ * Real.exp (-b₃ * (Real.log T) ^ 2) := by positivity
  calc
    _ = ENNReal.ofReal
      (a₀ * Real.exp (-b₀ * (Real.log T) ^ 2) +
       a₁ * Real.exp (-b₁ * (Real.log T) ^ 2) +
       a₂ * Real.exp (-b₂ * (Real.log T) ^ 2) +
       a₃ * Real.exp (-b₃ * (Real.log T) ^ 2)) := by
      rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hnonneg₀ hnonneg₁) hnonneg₂) hnonneg₃,
        ENNReal.ofReal_add (add_nonneg hnonneg₀ hnonneg₁) hnonneg₂,
        ENNReal.ofReal_add hnonneg₀ hnonneg₁]
    _ ≤ ENNReal.ofReal ((a₀ + a₁ + a₂ + a₃) * Real.exp
        (-(min (min b₀ b₁) (min b₂ b₃)) * (Real.log T) ^ 2)) :=
      ENNReal.ofReal_le_ofReal (by simpa only [b] using hsum)

end SupercriticalLQGUniqueness.B2.DG20Pt
