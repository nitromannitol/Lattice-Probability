/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.PositiveHeatTrunc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsMedian

/-! Scratch freeze split of SLUField.lean:178. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- The truncated heat kernel `w ↦ p_s(z, w) χ_n(w)` (DG l. 284; `LQGMetric.heatTrunc`) on its
source carrier: positive times `s > 0` only. -/
def positiveHeatTrunc (s : Set.Ioi (0 : ℝ)) (z : ℂ) (n : ℕ) : TestC :=
  heatTrunc (s : ℝ) z n
end SupercriticalLQGUniqueness
