/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingAdapter
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenCountable

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_measurable_lfppCrossingLength (ξ : ℝ) :
    Measurable (fun φ : C(ℂ, ℝ) => lfppCrossingLength ξ φ) := by
  have hm : Measurable (fun φ : C(ℂ, ℝ) =>
      crossLenIn ξ φ (rectAB 1 1).toSet
        (rectAB 1 1).side₁ (rectAB 1 1).side₂) :=
    measurable_crossLenIn (rectAB 1 1).isCompact_toSet
      (fun φ => φ.continuous) (fun z => continuous_eval_const z |>.measurable)
  simpa only [dg20_lfppCrossingLength_eq_rectLen, rectLen] using hm

end SupercriticalLQGUniqueness.B2.DG20Pt
