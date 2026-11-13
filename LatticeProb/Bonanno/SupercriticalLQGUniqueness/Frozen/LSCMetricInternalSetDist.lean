/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricInternalSetDist at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.ScaleTranslateDist

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `LSCMetric.internalSetDist`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


namespace LSCMetric

/-- DG l. 458 with l. 424–429: the `D`-internal distance `D (K₁, K₂; U)` between subsets `K₁, K₂`
of `U`, the infimum over `x ∈ K₁`, `y ∈ K₂` of the internal metric `D (x, y; U)` (`∞` if a set is
empty). The sets are subsets of the carrier `U` of the internal metric. -/
def internalSetDist (D : LSCMetric) (U : Set ℂ) (K₁ K₂ : Set U) : ℝ≥0∞ :=
  ⨅ (x ∈ K₁) (y ∈ K₂), D.internal U (x, y)

end LSCMetric

end SupercriticalLQGUniqueness
