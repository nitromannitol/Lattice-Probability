/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTIgChi at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.igChi`

`χ = 2/√κ − √κ/2` for `κ = γ²`; positive for `γ ∈ (0, 2)` (S1Y probe N5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Imaginary-geometry constant `χ = 2/√κ − √κ/2` for the flow-line parameter `κ = γ² = 16/κ'` (IG1, (4.1);
[18]; [20]). -/
def igChi (γ : ℝ) : ℝ := 2 / γ - γ / 2

end MatedCRT

end MatedCRTHarmonic
