/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTConeScale at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTConeLogRadial

/-!
# Frozen definition: `MatedCRT.coneScale`

Read off the radial process (no circle-average junk); non-junk a.s.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **`R_b`** : `R_b = sup {r > 0 | h_r(0) + Q log r = γ⁻¹ log b}`, read off the radial process (no circle
average junk): `R_b = exp (sup {s | A_{−s} + Q s = γ⁻¹ log b})`. -/
def coneScale (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (b₀ : ℝ) : ℝ :=
  Real.exp (sSup {s : ℝ | coneLogRadial γ α b b' s = γ⁻¹ * Real.log b₀})

end MatedCRT

end MatedCRTHarmonic
