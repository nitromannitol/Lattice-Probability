/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LfppCrossingLength at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.CrossingLFPP

/-! Scratch freeze split of SLUField.lean:200. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- `inf {∫₀¹ e^{ξ φ(P(t))} |P'(t)| dt : P a left–right crossing of [0,1]²}` (DG (1.4),
l. 297), for a continuous field `φ : C(ℂ, ℝ)`. -/
def lfppCrossingLength (ξ : ℝ) (φ : C(ℂ, ℝ)) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ) (hP : IsLeftRightCrossing P), crossingLFPP ξ φ P hP
end SupercriticalLQGUniqueness
