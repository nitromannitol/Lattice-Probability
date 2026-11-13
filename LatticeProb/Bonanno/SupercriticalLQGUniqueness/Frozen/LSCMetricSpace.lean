/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInstMeasurableSpace

/-! Scratch freeze split of SLUMetric.lean:123. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- The extended metric space `(α, D)`: a type synonym of `ℂ`, carrying the topology of the
extended metric `D` (not the Euclidean topology of `ℂ`). -/
def Space (_D : LSCMetric) : Type := ℂ
end LSCMetric
end SupercriticalLQGUniqueness
