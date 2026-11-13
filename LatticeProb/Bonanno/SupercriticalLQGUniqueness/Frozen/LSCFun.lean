/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCFun at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCTendsto

/-! Scratch freeze split of SLUMetric.lean:67. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- The lower semicontinuous functions `ℂ × ℂ → ℝ ∪ {-∞, +∞}` (DG l. 312–313). -/
def LSCFun : Type :=
  {f : ℂ × ℂ → EReal // LowerSemicontinuous f}
end SupercriticalLQGUniqueness
