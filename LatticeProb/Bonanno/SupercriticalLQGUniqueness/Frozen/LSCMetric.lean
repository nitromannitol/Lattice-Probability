/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetric at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCFunInstTopologicalSpace

/-! Scratch freeze split of SLUMetric.lean:88. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- The lower semicontinuous metrics on `ℂ` (DG l. 430–431): extended metrics `d` on `ℂ` such
that `(x, y) ↦ d (x, y)` is lower semicontinuous on `ℂ × ℂ`. -/
def LSCMetric : Type :=
  {d : ℂ × ℂ → ℝ≥0∞ // IsExtMetric d ∧ LowerSemicontinuous d}
end SupercriticalLQGUniqueness
