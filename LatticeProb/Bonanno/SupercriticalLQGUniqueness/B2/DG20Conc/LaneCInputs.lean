/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BBlocks
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.D5T
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

def sourceRadius (K m : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (K - m)

def sourceAround (K m : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  {z | sourceRadius K m < dist z (T20.dyCenter K b) ∧
    dist z (T20.dyCenter K b) < 2 * sourceRadius K m}

def sourceInner (K m : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  sphere (T20.dyCenter K b) (sourceRadius K m)

def sourceOuter (K m : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  sphere (T20.dyCenter K b) (2 * sourceRadius K m)

 
end SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
