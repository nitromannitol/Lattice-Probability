/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTConeRescaleCurve at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.coneRescaleCurve`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **`η^b`** : `η^b(t) = R_b⁻¹ η(bt)`. -/
def coneRescaleCurve (R b₀ : ℝ) (η : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => ((R⁻¹ : ℝ) : ℂ) * η (b₀ * t), by fun_prop⟩

end MatedCRT

end MatedCRTHarmonic
