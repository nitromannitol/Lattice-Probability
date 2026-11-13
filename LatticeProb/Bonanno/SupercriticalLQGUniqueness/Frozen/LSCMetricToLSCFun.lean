/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricToLSCFun at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Support.LSCMetricLowerSemicontinuous

/-! Scratch freeze split of SLUMetric.lean:105. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- A lower semicontinuous metric, viewed as a lower semicontinuous function with values in
`ℝ ∪ {-∞, +∞}`. -/
def toLSCFun (D : LSCMetric) : LSCFun :=
  ⟨fun p => ((D p : ℝ≥0∞) : EReal),
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous D.lowerSemicontinuous
      EReal.coe_ennreal_strictMono.monotone⟩
end LSCMetric
end SupercriticalLQGUniqueness
