/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.EuclideanAnnulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInternal

/-! Scratch freeze split of SLUMetric.lean:167. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- A Euclidean annulus `𝔸_{r₁,r₂}(c)` with `0 < r₁ < r₂ < ∞` (DG l. 978–980, 573). -/
def EuclideanAnnulus : Type :=
  {t : ℂ × (ℝ × ℝ) // 0 < t.2.1 ∧ t.2.1 < t.2.2}
end SupercriticalLQGUniqueness
