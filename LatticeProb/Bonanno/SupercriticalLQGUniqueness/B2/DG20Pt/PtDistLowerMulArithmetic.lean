/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLowerMulArithmetic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleArithmetic

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_lower_mul_event
    (c T lam : ℝ) (hc : 0 < c) (hT : 0 < T)
    (D E : ℝ≥0∞)
    (hED : E ≤ ENNReal.ofReal c * D)
    (hD : D < ENNReal.ofReal ((c * T)⁻¹ * lam)) :
    E < ENNReal.ofReal (T⁻¹ * lam) := by
  have hct : 0 < c * T := mul_pos hc hT
  have hmul :
      ENNReal.ofReal c * ENNReal.ofReal ((c * T)⁻¹ * lam) =
        ENNReal.ofReal (T⁻¹ * lam) := by
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    field_simp
  calc
    E ≤ ENNReal.ofReal c * D := hED
    _ < ENNReal.ofReal c *
        ENNReal.ofReal ((c * T)⁻¹ * lam) := by
      simpa only [mul_comm] using
        ENNReal.mul_lt_mul_left
          (ENNReal.ofReal_pos.mpr hc).ne'
          ENNReal.ofReal_ne_top hD
    _ = ENNReal.ofReal (T⁻¹ * lam) := hmul

end SupercriticalLQGUniqueness.B2.DG20Pt
