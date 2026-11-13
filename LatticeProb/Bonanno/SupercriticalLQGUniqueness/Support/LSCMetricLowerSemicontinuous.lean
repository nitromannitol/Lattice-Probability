/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Support.LSCMetricLowerSemicontinuous at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Support.LSCMetricIsExtMetric

 
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

theorem lowerSemicontinuous (D : LSCMetric) : LowerSemicontinuous D := D.2.2
end LSCMetric
end SupercriticalLQGUniqueness
