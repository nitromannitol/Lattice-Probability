/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusCompare at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusOsc
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAroundCompare

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 

def laneBBlockAround (i : Bool) (v : ℂ) (K : ℕ) : Set ℂ :=
  (fun z => v + (2 : ℝ)⁻¹ ^ K • (z - (⟨1 / 2, 1 / 2⟩ : ℂ))) ''
    laneCUnitUaround i

 

end SupercriticalLQGUniqueness.B2.DG20Conc
