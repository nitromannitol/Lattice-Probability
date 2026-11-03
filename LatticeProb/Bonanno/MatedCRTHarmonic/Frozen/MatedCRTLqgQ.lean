/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTLqgQ at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.lqgQ`

`Q = 2/γ + γ/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- `Q = 2/γ + γ/2`. -/
def lqgQ (γ : ℝ) : ℝ := 2 / γ + γ / 2

end MatedCRT

end MatedCRTHarmonic
