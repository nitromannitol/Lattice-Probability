/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTConeField at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTOfFunC
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLateralPart

/-!
# Frozen definition: `MatedCRT.coneField`

Its circle average about `0` at radius `e^{−t}` is `A_t` almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **The circle-average embedding of a quantum cone** (DMS Def 4.10, DMS): lateral part of
the whole-plane GFF `X` plus the radial function `z ↦ A_{−log|z|}`, so that `h_{e^{-t}}(0) = A_t` and
`h − h_{|·|}(0)` is the lateral part of `X`. -/
def coneField (X : Field) (A : ℝ → ℝ) : Field :=
  lateralPart X + ofFunC (fun z => A (-Real.log ‖z‖))

end MatedCRT

end MatedCRTHarmonic
