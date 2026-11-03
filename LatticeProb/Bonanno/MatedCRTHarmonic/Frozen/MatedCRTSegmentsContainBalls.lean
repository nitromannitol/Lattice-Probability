/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTSegmentsContainBalls at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.SegmentsContainBalls`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **GHM15 Prop 3.4's event** `E_ε(R, r)` (GHM15): for every `δ ∈ (0, ε]` and `a < b` with
`c([a,b]) ⊂ B_R(0)` and `diam c([a,b]) ≥ δ^{1−r}`, the segment contains a ball of radius `δ`. -/
def SegmentsContainBalls (c : C(ℝ, ℂ)) (R r ε : ℝ) : Prop :=
  ∀ δ ∈ Ioc (0 : ℝ) ε, ∀ a b : ℝ, a < b → c '' Icc a b ⊆ ball 0 R →
    δ ^ (1 - r) ≤ diam (c '' Icc a b) → ∃ w : ℂ, ball w δ ⊆ c '' Icc a b

end MatedCRT

end MatedCRTHarmonic
