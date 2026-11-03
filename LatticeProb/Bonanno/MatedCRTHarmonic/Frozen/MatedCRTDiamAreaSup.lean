/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTDiamAreaSup at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.diamAreaSup`

`x/0 = ⊤` is not hit: cells have positive area .
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **`DA(H₀)`** of [20] (4.12): `sup_{s ∈ [0,1]} diam(c([s−1,s]))² / area(c([s−1,s]))`. -/
def diamAreaSup (c : C(ℝ, ℂ)) : ℝ≥0∞ :=
  ⨆ s ∈ Icc (0 : ℝ) 1, ENNReal.ofReal (diam (c '' Icc (s - 1) s) ^ 2) / volume (c '' Icc (s - 1) s)

end MatedCRT

end MatedCRTHarmonic
