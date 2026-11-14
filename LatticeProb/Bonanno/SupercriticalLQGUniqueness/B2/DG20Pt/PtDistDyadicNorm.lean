/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicNorm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLambdaLower

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_dyadic_norm_le (ξ Q ζ C lam : ℝ) (n : ℕ)
    (hC : 0 < C)
    (hlam : C⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ζ) * (n : ℝ)) ≤ lam) :
    (2 : ℝ) ^ (-(n : ℝ)) ≤
      C * lam * (2 : ℝ) ^ (-(ξ * Q - ζ) * (n : ℝ)) := by
  let A : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + ζ) * (n : ℝ))
  let B : ℝ := (2 : ℝ) ^ (-(ξ * Q - ζ) * (n : ℝ))
  have hpow : A * B = (2 : ℝ) ^ (-(n : ℝ)) := by
    dsimp [A, B]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hCinv : C * C⁻¹ = 1 := mul_inv_cancel₀ hC.ne'
  have hB : 0 ≤ B := by positivity
  have hmul := mul_le_mul_of_nonneg_right hlam (mul_nonneg hC.le hB)
  calc
    (2 : ℝ) ^ (-(n : ℝ)) = (C⁻¹ * A) * (C * B) := by
      rw [← hpow]
      calc
        A * B = (C * C⁻¹) * (A * B) := by rw [hCinv, one_mul]
        _ = (C⁻¹ * A) * (C * B) := by ring
    _ ≤ lam * (C * B) := hmul
    _ = C * lam * (2 : ℝ) ^ (-(ξ * Q - ζ) * (n : ℝ)) := by
      dsimp [B]
      ring

end SupercriticalLQGUniqueness.B2.DG20Pt
