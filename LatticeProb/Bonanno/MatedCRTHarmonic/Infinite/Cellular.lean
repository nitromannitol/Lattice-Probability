/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Infinite.Cellular at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellularFacts.Basic

/-!
# Cellular embeddings force infinitely many vertices

This adapter exposes the Section 5 consequence in the namespace used by the infinitude results.
-/

set_option autoImplicit false

namespace MatedCRTHarmonic.Infinite

open MatedCRTHarmonic

/-- A cellular embedding has infinitely many vertices; reuse the Section 5 compactness proof. -/
theorem infinite_of_cellularEmbedding {V E : Type*} {G : LFMultigraph V E} {o : V}
    (H : CellularEmbedding G o) : Infinite V :=
  MatedCRTHarmonic.CellularFacts.infinite_of_cellularEmbedding H

end MatedCRTHarmonic.Infinite
