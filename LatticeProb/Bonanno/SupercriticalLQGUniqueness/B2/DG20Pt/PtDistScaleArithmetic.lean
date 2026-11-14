/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleArithmetic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicLowerTail

 


set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_rescale_cancel (lam : ℝ) (hlam : 0 < lam) (D : ℝ≥0∞) :
    ENNReal.ofReal lam * (ENNReal.ofReal lam⁻¹ * D) = D := by
  have hprod : ENNReal.ofReal lam * ENNReal.ofReal lam⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hlam.le, mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]
  rw [← mul_assoc, hprod, one_mul]

theorem pt_dist_rescale_upper_bound
    (lam M : ℝ) (hlam : 0 < lam) (hM : 0 ≤ M)
    (D : ℝ≥0∞) (hD : D ≤ ENNReal.ofReal (M * lam)) :
    ENNReal.ofReal lam⁻¹ * D ≤ ENNReal.ofReal M := by
  have h : ENNReal.ofReal lam⁻¹ * D ≤
      ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (M * lam) := by gcongr
  have hprod : ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (M * lam) =
      ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le)]
    congr 1
    field_simp
  exact h.trans_eq hprod

theorem pt_dist_rescale_lower_event
    (lam T : ℝ) (hlam : 0 < lam) (hT : 0 < T)
    (D : ℝ≥0∞)
    (hD : ENNReal.ofReal lam⁻¹ * D < ENNReal.ofReal T⁻¹) :
    D < ENNReal.ofReal (T⁻¹ * lam) := by
  have h := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_pos.mpr hlam).ne' ENNReal.ofReal_ne_top hD
  rw [pt_dist_rescale_cancel lam hlam D] at h
  have hprod : ENNReal.ofReal lam * ENNReal.ofReal T⁻¹ =
      ENNReal.ofReal (T⁻¹ * lam) := by
    rw [← ENNReal.ofReal_mul hlam.le]
    congr 1
    ring
  exact h.trans_eq hprod

end SupercriticalLQGUniqueness.B2.DG20Pt
