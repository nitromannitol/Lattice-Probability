/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricPt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricSpace

/-! Scratch freeze split of SLUMetric.lean:126. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- The identity map from `ℂ` to `(α, D)`. -/
def pt (D : LSCMetric) : ℂ → D.Space := id
end LSCMetric
end SupercriticalLQGUniqueness
