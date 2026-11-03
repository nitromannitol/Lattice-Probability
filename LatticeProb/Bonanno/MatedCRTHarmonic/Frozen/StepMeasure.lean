/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.StepMeasure at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.OutDarts
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Deg
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace

/-!
# Frozen definition: `LFMultigraph.stepMeasure`

Literal, with no fallback branch: `deg x ≠ 0` by `exists_inc`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- One step of simple random walk from `x`: a uniformly chosen edge end at `x`. -/
def stepMeasure (x : V) : Measure G.State :=
  (G.deg x : ℝ≥0∞)⁻¹ • ∑ d ∈ G.outDarts x, Measure.dirac (show G.State from Sum.inr d)

end LFMultigraph

end MatedCRTHarmonic
