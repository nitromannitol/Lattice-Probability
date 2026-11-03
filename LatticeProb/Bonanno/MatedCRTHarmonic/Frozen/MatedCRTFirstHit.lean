/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTFirstHit at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.firstHit`

Non-junk by surjectivity and transience .
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- First hitting time of `z` by a curve (a.s. the unique hitting time of a fixed point). -/
def firstHit (c : C(ℝ, ℂ)) (z : ℂ) : ℝ := sInf {t : ℝ | c t = z}

end MatedCRT

end MatedCRTHarmonic
