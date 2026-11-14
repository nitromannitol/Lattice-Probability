/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointFieldFactor at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistPointGaussianSum
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFieldFactor

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_point_field_exp_factor
    (ξ L β u : ℝ) (k : ℕ) (hξ : 0 < ξ) (hβ : 0 ≤ β)
    (hfield : |u| ≤ (L + β * (k : ℝ)) / ξ) :
    Real.exp (ξ * u) ≤ Real.exp L *
      (2 : ℝ) ^ (2 * β * (k : ℝ)) := by
  have h0 : |u - 0| ≤
      (Real.log (Real.exp L) + β * (k : ℝ)) / ξ := by
    simpa only [sub_zero, Real.log_exp] using hfield
  have hcomp := pt_dist_exp_field_compare ξ (Real.exp L) β u 0 k
    hξ (Real.exp_pos L) h0
  have hpow := pt_dist_exp_linear_le_two_rpow_double β hβ k
  have hcomp' : Real.exp (ξ * u) ≤ Real.exp L *
      Real.exp (β * (k : ℝ)) := by
    simpa only [mul_one, mul_zero, Real.exp_zero] using hcomp
  exact hcomp'.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos L).le)

theorem pt_dist_point_field_weighted_factor
    (ξ Q ζ L β u : ℝ) (k : ℕ)
    (hξ : 0 < ξ) (hβ : 0 ≤ β)
    (hfield : |u| ≤ (L + β * (k : ℝ)) / ξ) :
    (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) * Real.exp (ξ * u) ≤
      Real.exp L * (2 : ℝ) ^
        (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ)) := by
  have hpow : (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) *
      (2 : ℝ) ^ (2 * β * (k : ℝ)) =
      (2 : ℝ) ^ (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ ≤ (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) *
      (Real.exp L * (2 : ℝ) ^ (2 * β * (k : ℝ))) := by
        gcongr
        exact pt_dist_point_field_exp_factor ξ L β u k hξ hβ hfield
    _ = _ := by rw [← mul_assoc, mul_comm ((2 : ℝ) ^ _), mul_assoc, hpow]

end SupercriticalLQGUniqueness.B2.DG20Pt
