/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTConeLogRadial at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLqgQ
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeRadial

/-!
# Frozen definition: `MatedCRT.coneLogRadial`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The radial path `s ↦ A_{−s} + Q s` of the cone (`= h_{e^s}(0) + Q s`). -/
def coneLogRadial (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (s : ℝ) : ℝ := coneRadial γ α b b' (-s) + lqgQ γ * s

end MatedCRT

end MatedCRTHarmonic
