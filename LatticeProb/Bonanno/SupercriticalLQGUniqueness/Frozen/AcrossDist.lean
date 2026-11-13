/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.AcrossDist at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.Disconnects

/-! Scratch freeze split of SLUMetric.lean:207. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- DG Definition 1.11 (l. 555): `D (across A)`, the `D`-distance between the inner and outer
boundaries of the Euclidean annulus `A`. -/
def acrossDist (D : LSCMetric) (A : EuclideanAnnulus) : ℝ≥0∞ :=
  ⨅ (x ∈ A.innerBoundary) (y ∈ A.outerBoundary), D (x, y)
end SupercriticalLQGUniqueness
