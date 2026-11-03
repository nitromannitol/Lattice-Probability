/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.StateVertex at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dtgt
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State

/-!
# Frozen definition: `LFMultigraph.stateVertex`

The current vertex of a state.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The current vertex of a state. -/
def stateVertex (s : G.State) : V := Sum.elim id G.dtgt (s : V ⊕ G.Dart)

end LFMultigraph

end MatedCRTHarmonic
