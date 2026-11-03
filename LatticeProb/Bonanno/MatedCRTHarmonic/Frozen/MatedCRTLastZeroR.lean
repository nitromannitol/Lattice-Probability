/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTLastZeroR at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.lastZeroR`

The same body as QuantumZipper `lastZero` (`rfl`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Last zero on `[0, ∞)` of a path (QuantumZipper `lastZero`): `sup {s ≥ 0 | c s = 0}`. -/
def lastZeroR (c : ℝ → ℝ) : ℝ := sSup {s : ℝ | 0 ≤ s ∧ c s = 0}

end MatedCRT

end MatedCRTHarmonic
