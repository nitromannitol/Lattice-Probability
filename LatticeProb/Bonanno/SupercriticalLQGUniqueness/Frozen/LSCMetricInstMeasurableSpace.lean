/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricInstMeasurableSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInstTopologicalSpace

/-! Scratch freeze split of SLUMetric.lean:116. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- DG l. 432: the Borel σ-algebra of that topology. -/
@[reducible, instance] def instMeasurableSpace : MeasurableSpace (LSCMetric) :=
  borel (LSCMetric)
end LSCMetric
end SupercriticalLQGUniqueness
