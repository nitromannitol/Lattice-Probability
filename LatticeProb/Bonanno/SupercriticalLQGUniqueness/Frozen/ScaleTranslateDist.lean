/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.ScaleTranslateDist at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.TestDilate

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `scaleTranslateDist`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- The field `h(r · + z)` for `r > 0` (DG Axiom IV, l. 454–456):
`⟨h(r · + z), φ⟩ = r⁻² ⟨h, φ((· - z)/r)⟩`, the change of variables `y = r x + z` in `ℝ²`. -/
def scaleTranslateDist (r : Set.Ioi (0 : ℝ)) (z : ℂ) (h : DistC) : DistC :=
  ((r : ℝ) ^ 2)⁻¹ • h.comp (testDilate r z)

end SupercriticalLQGUniqueness
