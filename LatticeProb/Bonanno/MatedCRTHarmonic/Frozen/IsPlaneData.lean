/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.IsPlaneData at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj

/-!
# Frozen definition: `LFMultigraph.IsPlaneData`

Literal.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- §3 plane data `K = {J_x}`. -/
structure IsPlaneData (J : V → Set ℂ) : Prop where
  isConnected : ∀ x, IsConnected (J x)
  isBounded : ∀ x, Bornology.IsBounded (J x)
  locallyFinite : LocallyFinite J
  inter_of_adj : ∀ x y, G.adj.Adj x y → (J x ∩ J y).Nonempty

end LFMultigraph

end MatedCRTHarmonic
