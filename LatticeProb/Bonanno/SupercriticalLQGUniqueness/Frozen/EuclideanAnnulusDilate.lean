/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusDilate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusOuterBoundary

/-! Scratch freeze split of SLUMetric.lean:194. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace EuclideanAnnulus

/-- The dilation `r A = {r z : z ∈ A}` for `r > 0` (DG l. 576–577); see `toSet_dilate`. -/
def dilate (A : EuclideanAnnulus) (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨(r • A.center, r * A.innerRadius, r * A.outerRadius),
    mul_pos hr A.2.1, mul_lt_mul_of_pos_left A.2.2 hr⟩
end EuclideanAnnulus
end SupercriticalLQGUniqueness
