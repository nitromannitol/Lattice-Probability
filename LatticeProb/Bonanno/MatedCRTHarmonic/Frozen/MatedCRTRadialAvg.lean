/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTRadialAvg at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField

/-!
# Frozen definition: `MatedCRT.radialAvg`

The radial circle-average process of the mated-CRT cone field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The radial profile `z ↦ h_{|z|}(0)` (circle averages about `0`, LQGMetric `circleAvg`). -/
def radialAvg (h : Field) : ℂ → ℝ := fun z => LQGMetric.circleAvg h ‖z‖ 0

end MatedCRT

end MatedCRTHarmonic
