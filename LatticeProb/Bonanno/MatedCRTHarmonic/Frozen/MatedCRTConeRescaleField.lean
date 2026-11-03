/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTConeRescaleField at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLqgQ

/-!
# Frozen definition: `MatedCRT.coneRescaleField`

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **`h_b`** : `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b`. -/
def coneRescaleField (γ R b₀ : ℝ) (h : Field) : Field :=
  LQGMetric.addConst (LQGMetric.affineComp R 0 h) (lqgQ γ * Real.log R - γ⁻¹ * Real.log b₀)

end MatedCRT

end MatedCRTHarmonic
