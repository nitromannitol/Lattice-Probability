/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFieldFactor at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGoodSite
import Mathlib.Analysis.Complex.ExponentialBounds

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_exp_field_compare (ξ T ζ u v : ℝ) (k : ℕ)
    (hξ : 0 < ξ) (hT : 0 < T)
    (hfield : |u - v| ≤ (Real.log T + ζ * (k : ℝ)) / ξ) :
    Real.exp (ξ * u) ≤ T * Real.exp (ζ * (k : ℝ)) * Real.exp (ξ * v) := by
  have hdiff : ξ * (u - v) ≤ Real.log T + ζ * (k : ℝ) := by
    have h := le_trans (le_abs_self (u - v)) hfield
    simpa [mul_comm] using (le_div_iff₀ hξ).mp h
  have hexp : Real.exp (ξ * u) ≤ Real.exp (Real.log T + ζ * (k : ℝ) + ξ * v) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (ξ * u) ≤ Real.exp (Real.log T + ζ * (k : ℝ) + ξ * v) := hexp
    _ = T * Real.exp (ζ * (k : ℝ)) * Real.exp (ξ * v) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hT]

 

theorem pt_dist_exp_linear_le_two_rpow_double (ζ : ℝ) (hζ : 0 ≤ ζ) (k : ℕ) :
    Real.exp (ζ * (k : ℝ)) ≤ (2 : ℝ) ^ (2 * ζ * (k : ℝ)) := by
  have hlog : (1 : ℝ) ≤ 2 * Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hz : 0 ≤ ζ * (k : ℝ) := mul_nonneg hζ (Nat.cast_nonneg k)
  calc
    Real.exp (ζ * (k : ℝ)) ≤ Real.exp (Real.log 2 * (2 * ζ * (k : ℝ))) :=
      Real.exp_le_exp.mpr (by nlinarith)
    _ = (2 : ℝ) ^ (2 * ζ * (k : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

 



theorem pt_dist_site_cost_compare (ξ Q T ζ u v : ℝ) (k : ℕ)
    (hξ : 0 < ξ) (hT : 0 < T) (hζ : 0 ≤ ζ)
    (hfield : |u - v| ≤ (Real.log T + ζ * (k : ℝ)) / ξ) :
    Real.exp (ξ * u) * (T * (2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ))) ≤
      T ^ 2 * (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) * Real.exp (ξ * v) := by
  have h1 := pt_dist_exp_field_compare ξ T ζ u v k hξ hT hfield
  have h2 := pt_dist_exp_linear_le_two_rpow_double ζ hζ k
  have hpow : (2 : ℝ) ^ (2 * ζ * (k : ℝ)) *
      (2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ)) =
      (2 : ℝ) ^ (-(ξ * Q - 3 * ζ) * (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ ≤ (T * Real.exp (ζ * (k : ℝ)) * Real.exp (ξ * v)) *
        (T * (2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ))) := by
      gcongr
    _ ≤ (T * (2 : ℝ) ^ (2 * ζ * (k : ℝ)) * Real.exp (ξ * v)) *
        (T * (2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ))) := by
      gcongr
    _ = T ^ 2 * ((2 : ℝ) ^ (2 * ζ * (k : ℝ)) *
        (2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ))) * Real.exp (ξ * v) := by ring
    _ = _ := by rw [hpow]

end SupercriticalLQGUniqueness.B2.DG20Pt
