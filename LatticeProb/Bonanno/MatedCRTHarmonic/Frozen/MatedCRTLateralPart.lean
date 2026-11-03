/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTLateralPart at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTOfFunC
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTRadialAvg

/-!
# Frozen definition: `MatedCRT.lateralPart`

The lateral part of the mated-CRT cone field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The lateral part `h − h_{|·|}(0)` (projection onto the functions with mean zero on circles about `0`; DMS Def 4.10, DMS). -/
def lateralPart (h : Field) : Field := h - ofFunC (radialAvg h)

end MatedCRT

end MatedCRTHarmonic
