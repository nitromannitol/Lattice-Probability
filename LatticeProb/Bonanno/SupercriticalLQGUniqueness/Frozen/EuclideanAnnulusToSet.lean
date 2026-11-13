/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusToSet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusOuterRadius

/-! Scratch freeze split of SLUMetric.lean:182. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace EuclideanAnnulus

/-- The annulus as a subset of `ℂ`. -/
def toSet (A : EuclideanAnnulus) : Set ℂ :=
  Metric.ball A.center A.outerRadius \ closure (Metric.ball A.center A.innerRadius)
end EuclideanAnnulus
end SupercriticalLQGUniqueness
