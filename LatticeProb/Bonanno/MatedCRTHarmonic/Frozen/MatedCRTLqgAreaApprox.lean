/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTLqgAreaApprox at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDyadicScale

/-!
# Frozen definition: `MatedCRT.lqgAreaApprox`

The circle averages are LQGMetric `circleAvg` (a `limUnder`), correct for a.e. `z` a.s. .
With R1 the bundle quantifies over every dyadic vague limit; its a.s. existence for both cone fields is the closure
anchor R4 NJ1 (proved, `MesoModel/FrozenIdentities.lean`), not an input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The area approximation `2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz`. -/
def lqgAreaApprox (γ : ℝ) (h : Field) (k : ℕ) : Measure ℂ :=
  volume.withDensity fun z : ℂ =>
    ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * LQGMetric.circleAvg h (dyadicScale k) z))

end MatedCRT

end MatedCRTHarmonic
