module

/-
# Adding prescribed endpoints to finite polygonal chains

Attaching the two endpoint segments preserves the finite chain trace exactly
as the union of those segments and the original middle chain.
-/
public import LatticeProb.Topology.PolygonalChain

@[expose] public section



open Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Prepending a vertex adds the segment to the previous first vertex. -/
theorem polygonal_chain_cons_of_ne_nil (a : E) {vs : List E} (hv : vs ≠ []) :
    polygonalChain (a :: vs) = segment ℝ a (vs.head hv) ∪ polygonalChain vs := by
  cases vs with
  | nil => exact (hv rfl).elim
  | cons v rest => rfl

/-- **Polygonal Chain Endpoints.** Restoring two endpoints adds exactly the two endpoint segments. -/
theorem polygonal_chain_add_endpoints (a b : E) {vs : List E} (hv : vs ≠ []) :
    polygonalChain ((a :: vs) ++ [b]) =
      (segment ℝ a (vs.head hv) ∪ polygonalChain vs) ∪ segment ℝ (vs.getLast hv) b := by
  rw [polygonal_chain_concat (List.cons_ne_nil a vs) b,
    polygonal_chain_cons_of_ne_nil a hv, List.getLast_cons hv]

end LatticeProb.Topology
