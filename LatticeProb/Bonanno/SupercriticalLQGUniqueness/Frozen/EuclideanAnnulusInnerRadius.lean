/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusInnerRadius at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusCenter

/-! Scratch freeze split of SLUMetric.lean:176. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace EuclideanAnnulus

/-- Inner radius of a valid Euclidean annulus. -/
def innerRadius (A : EuclideanAnnulus) : ℝ := A.1.2.1
end EuclideanAnnulus
end SupercriticalLQGUniqueness
