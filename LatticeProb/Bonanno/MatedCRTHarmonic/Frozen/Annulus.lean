/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.Annulus at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `annulus`

Open balls used for annuli.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

variable {V : Type*}

/-- `A_{r,s}(z) = B_s(z) \ B_r(z)` (open balls). -/
def annulus (z : ℂ) (r s : ℝ) : Set ℂ := ball z s \ ball z r

end MatedCRTHarmonic
