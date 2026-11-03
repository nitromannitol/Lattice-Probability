/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.PlaneDiam at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `planeDiam`

Junk: `diam` of an unbounded set is `0`; only bounded sets occur.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

variable {V : Type*}

/-- `D_K(A) = diam U_A^K`, `U_A^K = ⋃_{x ∈ A} J_x`. -/
def planeDiam (J : V → Set ℂ) (A : Set V) : ℝ := diam (⋃ x ∈ A, J x)

end MatedCRTHarmonic
