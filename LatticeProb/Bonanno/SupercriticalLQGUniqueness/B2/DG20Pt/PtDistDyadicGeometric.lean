/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicGeometric at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenConnectedFinite

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_dyadic_power_eq_geometric (α : ℝ) (k : ℕ) :
    (2 : ℝ) ^ (-α * (k : ℝ)) = ((2 : ℝ) ^ (-α)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

end SupercriticalLQGUniqueness.B2.DG20Pt
