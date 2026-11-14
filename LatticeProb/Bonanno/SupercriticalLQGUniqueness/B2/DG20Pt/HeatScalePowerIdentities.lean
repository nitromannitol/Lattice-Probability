/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatScalePowerIdentities at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_rpow_complement {r : ℝ} (hr : 0 < r) (a : ℝ) :
    r ^ a * r ^ (1 - a) = r := by
  rw [← Real.rpow_add hr]
  convert Real.rpow_one r using 1 <;> ring

theorem dg20_rpow_scale_inverse {r : ℝ} (hr : 0 < r) (a : ℝ) :
    r * (r⁻¹) ^ a = r ^ (1 - a) := by
  rw [← Real.rpow_neg_eq_inv_rpow]
  nth_rewrite 1 [← Real.rpow_one r]
  rw [← Real.rpow_add hr]
  congr 1

end SupercriticalLQGUniqueness.B2.DG20Pt
