/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricInstTopologicalSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricToLSCFun

/-! Scratch freeze split of SLUMetric.lean:112. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- DG l. 432: the set of lower semicontinuous metrics carries the topology on lower
semicontinuous functions of DG Definition 1.2, i.e. the subspace topology of `LSCFun`. -/
@[reducible, instance] def instTopologicalSpace : TopologicalSpace (LSCMetric) :=
  TopologicalSpace.induced toLSCFun LSCFun.instTopologicalSpace
end LSCMetric
end SupercriticalLQGUniqueness
