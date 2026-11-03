/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTOfFunC at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField

/-!
# Frozen definition: `MatedCRT.ofFunC`

Junk `0` when `f` is not locally integrable; not hit by the cone radial profile a.s. .
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The distribution `φ ↦ ∫ f φ` of a function (junk `0` if `f` is not locally integrable; mathlib `ofFun`). -/
def ofFunC (f : ℂ → ℝ) : Field := Distribution.ofFun ⊤ f volume ⊤

end MatedCRT

end MatedCRTHarmonic
