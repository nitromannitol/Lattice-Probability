/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTGraph at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTSideCond
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite

/-!
# Frozen definition: `MatedCRT.graph`

Built from a proof of local finiteness (no junk branch); connected (`matedCRT_graph_connected`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **The ε-mated-CRT map of [18] (1.1)** `G^ε` of the path `ω`, as a locally finite multigraph on
`ℤ ≅ εℤ` with the explicit edge type `Edge ε ω`, built from a proof of local finiteness (no junk branch). Root: the
vertex `0` (`o := 0`). -/
def graph (ε : ℝ) (ω : Path2) (h : IsLocallyFinite ε ω) : LFMultigraph ℤ (Edge ε ω) where
  src e := e.1.1
  tgt e := e.1.2.1
  finite_inc := h
  exists_inc x := ⟨⟨(x, x + 1, false), lt_add_one x, Or.inl ⟨rfl, rfl⟩⟩, Or.inl rfl⟩

end MatedCRT

end MatedCRTHarmonic
