/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareFieldSplit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRadius
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Path
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Glue3
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneB_unit_square_subset_bigBox :
    (rectAB 1 1).toSet ⊆ T20D.bigBox := by
  intro x hx
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc,
    zero_add] at hx
  simp only [T20D.bigBox, Complex.mem_reProdIm, mem_Icc]
  rcases hx with ⟨⟨hxr0, hxr1⟩, ⟨hxi0, hxi1⟩⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

 

end SupercriticalLQGUniqueness.B2.DG20Conc
