/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Support.LSCMetricInstCoeFun at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetric

 
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

instance instCoeFun : CoeFun (LSCMetric) (fun _ => ℂ × ℂ → ℝ≥0∞) := ⟨fun D => D.1⟩
end LSCMetric
end SupercriticalLQGUniqueness
