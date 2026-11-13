/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LfppPathLength at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `lfppPathLength`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- LFPP length `∫₀¹ e^{ξ φ(P(t))} |P'(t)| dt` (DG (1.3), l. 292) on its source domain, the
piecewise continuously differentiable paths `P : [0,1] → ℂ` from `z` to `w` (l. 294). The proof
argument is erased; the value is definitionally the reused `LQGMetric.lfppLen` on that domain
(as `crossingLFPP`). -/
def lfppPathLength (ξ : ℝ) (φ : C(ℂ, ℝ)) (P : ℝ → ℂ) {z w : ℂ}
    (_ : IsPiecewiseC1Path P z w) : ℝ≥0∞ :=
  lfppLen ξ (⇑φ) P

end SupercriticalLQGUniqueness
