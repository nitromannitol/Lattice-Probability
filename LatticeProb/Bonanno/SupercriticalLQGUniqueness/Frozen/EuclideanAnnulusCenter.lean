/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusCenter at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.EuclideanAnnulus

/-! Scratch freeze split of SLUMetric.lean:173. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace EuclideanAnnulus

/-- Center of a valid Euclidean annulus. -/
def center (A : EuclideanAnnulus) : ℂ := A.1.1
end EuclideanAnnulus
end SupercriticalLQGUniqueness
