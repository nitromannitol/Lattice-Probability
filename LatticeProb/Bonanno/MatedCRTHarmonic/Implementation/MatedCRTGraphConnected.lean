/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Implementation.MatedCRTGraphConnected at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph

/-!
# Provider of the frozen theorem `matedCRT_graph_connected`

Proof of the theorem `MatedCRTHarmonic/Frozen/MatedCRTGraphConnected.lean`, connectivity of the ε-mated-CRT map
([18] (1.1)). This module states `MatedCRTHarmonic.Implementation.matedCRT_graph_connected_impl` with the
frozen statement verbatim (the anchor's ∀-form; same imports of frozen definition files, `open`s,
`noncomputable section` and `variable {V E : Type*}`) and proves it by a direct proof : consecutive vertices are adjacent. The theorem follows by `by exact MatedCRTHarmonic.Implementation.matedCRT_graph_connected_impl`. 
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Implementation

variable {V E : Type*}

-- The named hypothesis binders of the frozen ∀-form are part of the approved type, so the
-- unused-variables linter is silenced for this declaration only.
set_option linter.unusedVariables false in
/-- Provider of the frozen theorem `matedCRT_graph_connected` (statement verbatim). -/
theorem matedCRT_graph_connected_impl :
    ∀ (ε : ℝ) (ω : MatedCRT.Path2) (h : MatedCRT.IsLocallyFinite ε ω), (MatedCRT.graph ε ω h).adj.Connected :=
  by
    intro ε ω h
    have hadj : ∀ x : ℤ, (MatedCRT.graph ε ω h).adj.Adj x (x + 1) := by
      intro x
      rw [LFMultigraph.adj, SimpleGraph.fromRel_adj]
      exact ⟨by omega, Or.inl ⟨⟨(x, x + 1, false), lt_add_one x, Or.inl ⟨rfl, rfl⟩⟩, rfl, rfl⟩⟩
    have hr : ∀ x : ℤ, (MatedCRT.graph ε ω h).adj.Reachable 0 x := by
      intro x
      induction x using Int.induction_on with
      | zero => rfl
      | succ n ih => exact ih.trans (hadj n).reachable
      | pred n ih => exact ih.trans (by simpa using (hadj (-(n : ℤ) - 1)).symm.reachable)
    exact ⟨fun x y => (hr x).symm.trans (hr y)⟩

end MatedCRTHarmonic.Implementation
