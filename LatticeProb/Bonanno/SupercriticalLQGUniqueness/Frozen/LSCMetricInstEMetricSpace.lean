/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricInstEMetricSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricPt

/-! Scratch freeze split of SLUMetric.lean:128. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

@[reducible, instance] def instEMetricSpace (D : LSCMetric) : EMetricSpace D.Space where
  edist x y := D (x, y)
  edist_self x := D.isExtMetric.1 x
  edist_comm x y := D.isExtMetric.2.2.1 x y
  edist_triangle x y z := D.isExtMetric.2.2.2 x y z
  eq_of_edist_eq_zero {x y} h := D.isExtMetric.2.1 x y h
end LSCMetric
end SupercriticalLQGUniqueness
