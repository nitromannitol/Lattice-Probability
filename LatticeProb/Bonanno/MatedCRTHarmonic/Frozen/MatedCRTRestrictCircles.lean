/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTRestrictCircles at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.restrictCircles`

The `if` encodes the restriction `h|_V`, not a junk branch.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

open Classical in
/-- The circle-average process restricted to circles whose closed discs lie in `V` (junk `0` elsewhere): the
information `h|_V`. -/
def restrictCircles (V : Set ℂ) (H : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun ρ w => if 0 < ρ ∧ closedBall w ρ ⊆ V then H ρ w else 0

end MatedCRT

end MatedCRTHarmonic
