/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTLrCov at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.lrCov`

Unit-time covariance matrix `[[1, c], [c, 1]]`, `c = −cos(πγ²/4)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The covariance matrix per unit time of the Brownian pair of [18] §1.1 : `Var(L_1) = Var(R_1) = 1`,
`Cov(L_1, R_1) = −cos(πγ²/4)`. -/
def lrCov (γ : ℝ) (i j : Fin 2) : ℝ := if i = j then 1 else -Real.cos (Real.pi * γ ^ 2 / 4)

end MatedCRT

end MatedCRTHarmonic
