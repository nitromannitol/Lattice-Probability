import LatticeProb.Prob.Percolation.OpenGraphTranslation
import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-!
# Translation of actual open components

The graph isomorphism induces a bijection on every actual component, finite or infinite.
Its support is exactly the image under vertex addition. Unique infinitude and the selected
infinite component are transported only when the corresponding uniqueness hypothesis holds.
-/

namespace LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- Transport all actual components using the graph isomorphism's quotient map. -/
def openComponentTranslation (z : Vertex d) (ω : Configuration d) :
    OpenComponent ω ≃ OpenComponent (configurationTranslation z ω) :=
  (openGraphTranslation z ω).connectedComponentEquiv

/-- The component of each vertex moves to the component of the translated vertex. -/
theorem openComponentTranslation_mk (z : Vertex d) (ω : Configuration d) (x : Vertex d) :
    openComponentTranslation z ω ((openGraph ω).connectedComponentMk x) =
      (openGraph (configurationTranslation z ω)).connectedComponentMk (x + z) := rfl

/-- Every translated support is characterized by subtracting the displacement. -/
theorem mem_openComponentTranslation_supp (z : Vertex d) (C : OpenComponent ω)
    (x : Vertex d) :
    x ∈ (openComponentTranslation z ω C).supp ↔ x - z ∈ C.supp := by
  exact (SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map
    (φ := openGraphTranslation z ω)).symm

/-- Adding the displacement preserves and reflects membership in every component support. -/
theorem add_mem_openComponentTranslation_supp (z : Vertex d) (C : OpenComponent ω)
    (x : Vertex d) :
    x + z ∈ (openComponentTranslation z ω C).supp ↔ x ∈ C.supp := by
  rw [mem_openComponentTranslation_supp, add_sub_cancel_right]

/-- The entire translated support is the image of the original support under addition. -/
theorem openComponentTranslation_supp (z : Vertex d) (C : OpenComponent ω) :
    (openComponentTranslation z ω C).supp = (fun x => x + z) '' C.supp := by
  ext x
  rw [mem_openComponentTranslation_supp]
  constructor
  · intro hx
    exact ⟨x - z, hx, sub_add_cancel x z⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [add_sub_cancel_right] using hy

/-- The component equivalence's inverse subtracts the displacement at every root. -/
theorem openComponentTranslation_symm_mk (z : Vertex d) (ω : Configuration d)
    (x : Vertex d) :
    (openComponentTranslation z ω).symm
        ((openGraph (configurationTranslation z ω)).connectedComponentMk x) =
      (openGraph ω).connectedComponentMk (x - z) := rfl

/-- The inverse component map recovers every original component. -/
theorem openComponentTranslation_symm_apply_apply (z : Vertex d) (C : OpenComponent ω) :
    (openComponentTranslation z ω).symm (openComponentTranslation z ω C) = C :=
  (openComponentTranslation z ω).symm_apply_apply C

/-- Every target component is recovered from its inverse image. -/
theorem openComponentTranslation_apply_symm_apply (z : Vertex d)
    (C : OpenComponent (configurationTranslation z ω)) :
    openComponentTranslation z ω ((openComponentTranslation z ω).symm C) = C :=
  (openComponentTranslation z ω).apply_symm_apply C

/-- Successive translations have the support of translation by the sum of displacements. -/
theorem openComponentTranslation_add_supp (z w : Vertex d) (C : OpenComponent ω) :
    (openComponentTranslation z (configurationTranslation w ω)
      (openComponentTranslation w ω C)).supp = (fun x => x + (z + w)) '' C.supp := by
  rw [openComponentTranslation_supp, openComponentTranslation_supp, Set.image_image]
  congr 1
  funext x
  exact (add_assoc x w z).trans (congrArg (x + ·) (add_comm w z))

/-- Infinitude is preserved and reflected for every actual component. -/
theorem openComponentTranslation_infinite_iff (z : Vertex d) (C : OpenComponent ω) :
    (openComponentTranslation z ω C).supp.Infinite ↔ C.supp.Infinite := by
  rw [openComponentTranslation_supp]
  exact Set.infinite_image_iff (fun _ _ _ _ h => add_right_cancel h)

/-- Existence and uniqueness of an infinite actual component is translation invariant. -/
theorem hasUniqueInfiniteOpenComponent_translation_iff (z : Vertex d) (ω : Configuration d) :
    HasUniqueInfiniteOpenComponent (configurationTranslation z ω) ↔
      HasUniqueInfiniteOpenComponent ω := by
  exact ((openComponentTranslation z ω).existsUnique_congr
    (fun C => (openComponentTranslation_infinite_iff z C).symm)).symm

/-- With actual uniqueness supplied, transport agrees with selection of the infinite component. -/
theorem openComponentTranslation_uniqueInfiniteComponent (z : Vertex d)
    (h : HasUniqueInfiniteOpenComponent ω) :
    openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent
        ((hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h) := by
  apply (eq_uniqueInfiniteComponent_iff _ _).mpr
  exact (openComponentTranslation_infinite_iff z _).mpr (uniqueInfiniteComponent_infinite h)

end LatticeProb.Percolation
