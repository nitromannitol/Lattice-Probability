/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.IsConnectedSet at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj

/-!
# Frozen definition: `LFMultigraph.IsConnectedSet`

The induced subgraph on `A` is connected.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- `A` is connected: its induced subgraph is connected. -/
def IsConnectedSet (A : Set V) : Prop := (G.adj.induce A).Connected

end LFMultigraph

end MatedCRTHarmonic
