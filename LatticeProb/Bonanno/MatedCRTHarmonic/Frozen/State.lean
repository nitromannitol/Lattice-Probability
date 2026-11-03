/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.State at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph

/-!
# Frozen definition: `LFMultigraph.State`

State space `V ⊕ Dart` of the edge-end walk : the start vertex at time `0`, then the dart just traversed.
Junk: a state `inl x` at a time `≥ 1` is never produced by the kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The state space of the edge-end walk: the start vertex (`Sum.inl x`, time `0` only) or the dart traversed at
the last step. Discrete σ-algebra. -/
def State (_G : LFMultigraph V E) : Type _ := V ⊕ (E × Bool)

end LFMultigraph

end MatedCRTHarmonic
