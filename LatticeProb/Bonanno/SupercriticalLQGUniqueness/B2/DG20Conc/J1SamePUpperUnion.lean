/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePUpperUnion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1ShiftRate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1ThresholdShift
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePRawSmall
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ThresholdExp
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUnitGeometry
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockUnion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockCrossLaw

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

def j1BlockAffineCenter (v : ℂ) (K : ℕ) : ℂ :=
  v - (((2 : ℝ)⁻¹ ^ K : ℝ) : ℂ) * (⟨1 / 2, 1 / 2⟩ : ℂ)

end SupercriticalLQGUniqueness.B2.DG20Conc
