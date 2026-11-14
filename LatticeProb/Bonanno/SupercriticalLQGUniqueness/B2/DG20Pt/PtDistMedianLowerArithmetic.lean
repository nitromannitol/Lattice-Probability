/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMedianLowerArithmetic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMedianNormCompare

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_median_lower_event
    (lam δ C T : ℝ) (hC : 0 < C) (hT : 0 < T)
    (hδ : δ ≤ C * lam) (D : ℝ≥0∞)
    (hD : D < ENNReal.ofReal ((C * T)⁻¹ * δ)) :
    D < ENNReal.ofReal (T⁻¹ * lam) := by
  have hct : 0 < C * T := mul_pos hC hT
  have hbudget : (C * T)⁻¹ * δ ≤ T⁻¹ * lam := by
    calc
      (C * T)⁻¹ * δ ≤ (C * T)⁻¹ * (C * lam) :=
        mul_le_mul_of_nonneg_left hδ (inv_nonneg.mpr hct.le)
      _ = T⁻¹ * lam := by field_simp
  exact hD.trans_le (ENNReal.ofReal_le_ofReal hbudget)

end SupercriticalLQGUniqueness.B2.DG20Pt
