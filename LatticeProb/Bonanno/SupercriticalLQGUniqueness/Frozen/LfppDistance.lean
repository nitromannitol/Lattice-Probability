/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LfppDistance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LfppPathLength

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `lfppDistance`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- The LFPP metric `D^ε_h(z, w) = inf_{P : z → w} ∫₀¹ e^{ξ h*_ε(P(t))} |P'(t)| dt` (DG (1.3),
l. 290–294) for a continuous field `φ` (in use, `φ = h*_ε`): the infimum over piecewise
continuously differentiable paths `P : [0,1] → ℂ` from `z` to `w`. -/
def lfppDistance (ξ : ℝ) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ) (hP : IsPiecewiseC1Path P p.1 p.2), lfppPathLength ξ φ P hP

end SupercriticalLQGUniqueness
