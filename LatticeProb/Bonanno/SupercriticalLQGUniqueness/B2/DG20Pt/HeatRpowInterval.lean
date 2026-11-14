/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatRpowInterval at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_rpow_interval_bounds {d t a : ℝ}
    (hd : 0 < d) (hdt : d ≤ t) (ht : t ≤ 1) :
    d ^ |a| ≤ t ^ a ∧ t ^ a ≤ d ^ (-|a|) := by
  have ht0 : 0 < t := lt_of_lt_of_le hd hdt
  constructor
  · exact (Real.rpow_le_rpow hd.le hdt (abs_nonneg a)).trans
      (Real.rpow_le_rpow_of_exponent_ge ht0 ht (le_abs_self a))
  · exact (Real.rpow_le_rpow_of_exponent_ge ht0 ht (neg_abs_le a)).trans
      (Real.rpow_le_rpow_of_nonpos hd hdt (neg_nonpos.mpr (abs_nonneg a)))

end SupercriticalLQGUniqueness.B2.DG20Pt
