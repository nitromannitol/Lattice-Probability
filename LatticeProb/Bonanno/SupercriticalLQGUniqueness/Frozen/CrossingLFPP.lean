/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.CrossingLFPP at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLeftRightCrossing

/-! Scratch freeze split of SLUField.lean:194. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- LFPP length on the source domain of piecewise-C¹ left–right crossings.
The proof argument is erased, and the value is definitionally the reused
`LQGMetric.lfppLen` on that domain. -/
def crossingLFPP (ξ : ℝ) (φ : C(ℂ, ℝ)) (P : ℝ → ℂ)
    (_ : IsLeftRightCrossing P) : ℝ≥0∞ :=
  lfppLen ξ (⇑φ) P
end SupercriticalLQGUniqueness
