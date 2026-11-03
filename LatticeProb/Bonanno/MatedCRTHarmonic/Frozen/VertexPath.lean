/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.VertexPath at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateVertex

/-!
# Frozen definition: `LFMultigraph.vertexPath`

The vertex path `X_n` of an edge-end path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The vertex path `X_n` of an edge-end path. -/
def vertexPath (ω : ℕ → G.State) : ℕ → V := fun n => G.stateVertex (ω n)

end LFMultigraph

end MatedCRTHarmonic
