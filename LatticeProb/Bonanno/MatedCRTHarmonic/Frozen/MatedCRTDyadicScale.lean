/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTDyadicScale at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.dyadicScale`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Dyadic scale `2^{-k}`. -/
def dyadicScale (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))

end MatedCRT

end MatedCRTHarmonic
