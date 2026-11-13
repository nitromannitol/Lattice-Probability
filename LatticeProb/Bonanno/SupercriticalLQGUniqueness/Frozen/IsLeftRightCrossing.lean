/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsLeftRightCrossing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.UnitSquare

/-! Scratch freeze split of SLUField.lean:187. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- `P` is a left–right crossing of `[0,1]²` (DG l. 299): a piecewise continuously
differentiable path `P : [0,1] → [0,1]²` joining the left side to the right side. -/
def IsLeftRightCrossing (P : ℝ → ℂ) : Prop :=
  IsPiecewiseC1Path P (P 0) (P 1) ∧ P 0 ∈ leftSide ∧ P 1 ∈ rightSide ∧
    ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ unitSquare
end SupercriticalLQGUniqueness
