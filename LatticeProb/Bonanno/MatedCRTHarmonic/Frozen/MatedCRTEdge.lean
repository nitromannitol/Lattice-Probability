/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTEdge at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsEdge

/-!
# Frozen definition: `MatedCRT.Edge`

The edge type of `G^ε`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The edge type of the ε-mated-CRT map of `ω`. -/
abbrev Edge (ε : ℝ) (ω : Path2) : Type := {e : ℤ × ℤ × Bool // IsEdge ε ω e}

end MatedCRT

end MatedCRTHarmonic
