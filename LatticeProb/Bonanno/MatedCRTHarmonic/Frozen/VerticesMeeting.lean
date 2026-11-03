/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.VerticesMeeting at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `verticesMeeting`

Literal.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

variable {V : Type*}

/-- `V_K(D) = {x : J_x ∩ D ≠ ∅}` (`𝒱_ℋ` of ). -/
def verticesMeeting (J : V → Set ℂ) (D : Set ℂ) : Set V := {x | (J x ∩ D).Nonempty}

end MatedCRTHarmonic
