/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusInnerBoundary at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusToSet

/-! Scratch freeze split of SLUMetric.lean:186. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace EuclideanAnnulus

/-- The inner boundary of `A` (DG l. 551): the circle of radius `r₁`. -/
def innerBoundary (A : EuclideanAnnulus) : Set ℂ :=
  Metric.sphere A.center A.innerRadius
end EuclideanAnnulus
end SupercriticalLQGUniqueness
