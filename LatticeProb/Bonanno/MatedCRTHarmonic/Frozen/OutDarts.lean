/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.OutDarts at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dsrc

/-!
# Frozen definition: `LFMultigraph.outDarts`

The edge ends at `x`, a finite set by local finiteness.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The edge ends at `x`: the darts leaving `x` (a finite set by local finiteness). -/
def outDarts (x : V) : Finset G.Dart := by
  classical
  exact ((G.finite_inc x).toFinset ×ˢ (Finset.univ : Finset Bool)).filter fun d => G.dsrc d = x

end LFMultigraph

end MatedCRTHarmonic
