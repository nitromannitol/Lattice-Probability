/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.CellularEmbedding at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj

/-!
# Frozen definition: `CellularEmbedding`

The interface allows loops allowed, planarity not used, connectivity
a theorem hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

/-- A cellular embedding: cells `H_x` indexed by vertices (the
bijection `ϕ`), compact, connected, with nonempty interior, locally finite, covering `ℂ`, with Lebesgue-null
pairwise intersections; adjacent vertices have intersecting cells; `0 ∈ H_o`. Finite multiplicities and local
finiteness are part of `LFMultigraph`; planarity of `G` is not used. -/
structure CellularEmbedding {V E : Type*} (G : LFMultigraph V E) (o : V) where
  cell : V → Set ℂ
  isCompact_cell : ∀ x, IsCompact (cell x)
  isConnected_cell : ∀ x, IsConnected (cell x)
  interior_cell_nonempty : ∀ x, (interior (cell x)).Nonempty
  locallyFinite_cell : LocallyFinite cell
  iUnion_cell : ⋃ x, cell x = Set.univ
  volume_inter_cell : ∀ x y, x ≠ y → volume (cell x ∩ cell y) = 0
  inter_of_adj : ∀ x y, G.adj.Adj x y → (cell x ∩ cell y).Nonempty
  zero_mem_root : (0 : ℂ) ∈ cell o

end MatedCRTHarmonic
