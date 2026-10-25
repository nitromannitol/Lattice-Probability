module

/-
# Finite polygonal chains and the Lattice-Probability plane

A finite chain gives a polygonal set in the existing library convention: a
finite union of closed segments. Linear maps also transport chains into that
convention, including the coordinate-pair to `Fin 2 → ℝ` equivalence.
-/
public import LatticeProb.Topology.PolygonalChain
public import LatticeProb.Topology.Polygonal

@[expose] public section



open Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of a chain under a linear map into the existing plane is polygonal. -/
theorem isPolygonal_image_polygonal_chain (f : E →ₗ[ℝ] Plane) :
    ∀ vs : List E, IsPolygonal (f '' polygonalChain vs)
  | [] => ⟨[], by simp⟩
  | [v] => by
    rw [polygonal_chain_singleton, image_singleton, ← segment_same ℝ (f v)]
    exact IsPolygonal.segment (f v) (f v)
  | u :: v :: rest => by
    rw [polygonal_chain_cons_cons, image_union]
    have hseg : f '' segment ℝ u v = segment ℝ (f u) (f v) :=
      image_segment ℝ f.toAffineMap u v
    rw [hseg]
    exact (IsPolygonal.segment (f u) (f v)).union
      (isPolygonal_image_polygonal_chain f (v :: rest))

/-- **Linear images of finite chains.** In particular, a chain in `LatticeProb.Plane` is an existing polygonal set. -/
theorem isPolygonal_polygonal_chain (vs : List Plane) : IsPolygonal (polygonalChain vs) := by
  have h := isPolygonal_image_polygonal_chain (LinearMap.id : Plane →ₗ[ℝ] Plane) vs
  simpa only [LinearMap.id_coe, image_id] using h

end LatticeProb.Topology
