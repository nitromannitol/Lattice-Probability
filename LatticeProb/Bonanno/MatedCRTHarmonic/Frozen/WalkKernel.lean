/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.WalkKernel at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateVertex
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasure

/-!
# Frozen definition: `LFMultigraph.walkKernel`

The time-homogeneous transition kernel of the edge-end walk: one step from the current vertex.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The transition kernel of the edge-end walk: step from the current vertex. -/
def walkKernel : Kernel G.State G.State where
  toFun s := G.stepMeasure (G.stateVertex s)
  measurable' := measurable_from_top

end LFMultigraph

end MatedCRTHarmonic
