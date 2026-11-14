/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundedCompare at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAroundCompare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 

theorem laneB_cutoff_factor_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (Q : PsiParams)
    (ξ x : ℝ) (ω : Ω) (hgood : T20C.Xbig Q W P ω ≤ x) :
    ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω)) ≤
      ENNReal.ofReal (Real.exp (|ξ| * x)) := by
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgood (abs_nonneg ξ))

 

end SupercriticalLQGUniqueness.B2.DG20Conc
