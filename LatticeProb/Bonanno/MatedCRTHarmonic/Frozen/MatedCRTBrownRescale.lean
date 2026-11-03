/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTBrownRescale at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2

/-!
# Frozen definition: `MatedCRT.brownRescale`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Brownian rescaling of the boundary-length pair: `t ↦ b^{-1/2} ω(bt)`. -/
def brownRescale (b₀ : ℝ) (ω : Path2) : Path2 :=
  ⟨fun t => (b₀ ^ (-(1 / 2 : ℝ))) • ω (b₀ * t), by fun_prop⟩

end MatedCRT

end MatedCRTHarmonic
