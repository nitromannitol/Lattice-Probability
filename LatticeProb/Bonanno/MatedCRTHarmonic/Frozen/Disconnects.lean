/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.Disconnects at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj

/-!
# Frozen definition: `LFMultigraph.Disconnects`

`U` meets every graph path joining `S` to `T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- `U` disconnects `S` from `T`: it meets every graph path joining them. -/
def Disconnects (U S T : Set V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ T, ∀ w : G.adj.Walk a b, ∃ y ∈ w.support, y ∈ U

end LFMultigraph

end MatedCRTHarmonic
