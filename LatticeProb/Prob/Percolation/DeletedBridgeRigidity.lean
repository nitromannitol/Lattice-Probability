import LatticeProb.Network.FiniteBridgeRigidity
import LatticeProb.Prob.Percolation.DeletedInfiniteComponent
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization

/-!
# Corrected planes on the separated-endpoint deletion branch

The singleton flip is the literal adjacent open bond. On the old actual component,
its full unordered-edge preimage is exactly the singleton subtype edge. Old and new
uniqueness are ordinary graph data; induced-component transport then supplies a finite
side and harmonic flux forces zero drop of the source corrected plane.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The complete unordered-edge preimage of an adjacent singleton bond is the singleton
edge on the actual component subtype, using injectivity of the subtype inclusion. -/
theorem deletedBondEdges_singleton_preimage (C : OpenComponent ω) {a b : C}
    (hab : (componentGraph C).Adj a b) :
    (Sym2.map (Subtype.val : C → Vertex d)) ⁻¹'
        deletedBondEdges {bondOfAdjacent ((openGraph_adj_iff ω a.val b.val).mp hab).choose} =
      (({s(a, b)} : Finset (Sym2 C)) : Set (Sym2 C)) := by
  classical
  have he : deletedBondEdges {bondOfAdjacent ((openGraph_adj_iff ω a.val b.val).mp hab).choose} =
      {s(a.val, b.val)} := by
    rw [deletedBondEdges, Finset.coe_singleton, Set.image_singleton]
    rfl
  rw [he]
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_singleton]
  change Sym2.map (Subtype.val : C → Vertex d) z =
      Sym2.map (Subtype.val : C → Vertex d) s(a, b) ↔ z = s(a, b)
  exact (Sym2.map.injective Subtype.val_injective).eq_iff

/-- Flipping the literal adjacent open bond deletes exactly the subtype edge on the old
component, with equality of the whole induced graph. -/
theorem singletonBondFlip_induce_eq_deleteEdges (C : OpenComponent ω) {a b : C}
    (hab : (componentGraph C).Adj a b) :
    (openGraph (finiteBondFlip
      {bondOfAdjacent ((openGraph_adj_iff ω a.val b.val).mp hab).choose} ω)).induce C.supp =
      (componentGraph C).deleteEdges
        (({s(a, b)} : Finset (Sym2 C)) : Set (Sym2 C)) := by
  classical
  have hopen : ∀ e ∈
      ({bondOfAdjacent ((openGraph_adj_iff ω a.val b.val).mp hab).choose} : Finset (Bond d)),
      ω e = true := by
    intro e he
    rw [Finset.mem_singleton.mp he]
    exact ((openGraph_adj_iff ω a.val b.val).mp hab).choose_spec
  rw [finiteBondFlip_induce_eq_deleteEdges _ hopen C,
    deletedBondEdges_singleton_preimage C hab]

/-- A source corrected plane has zero drop on an open edge whose singleton flip separates
the endpoints. Actual old/new infinite-component uniqueness supplies a finite side. -/
theorem correctedPlane_eq_of_singleton_flip_separates (C : OpenComponent ω)
    (hOld : HasUniqueInfiniteOpenComponent ω) (hC : C.supp.Infinite)
    {a b : C} (hab : (componentGraph C).Adj a b)
    (hNew : HasUniqueInfiniteOpenComponent
      (finiteBondFlip {bondOfAdjacent ((openGraph_adj_iff ω a.val b.val).mp hab).choose} ω))
    (hsep : ¬ ((openGraph
      (finiteBondFlip {bondOfAdjacent ((openGraph_adj_iff ω a.val b.val).mp hab).choose} ω)).induce
        C.supp).Reachable a b)
    {q : Fin d → ℝ} {u : C → ℝ} (hu : IsCorrectedPlane C q u) : u a = u b := by
  classical
  have hopen : ∀ e ∈
      ({bondOfAdjacent ((openGraph_adj_iff ω a.val b.val).mp hab).choose} : Finset (Bond d)),
      ω e = true := by
    intro e he
    rw [Finset.mem_singleton.mp he]
    exact ((openGraph_adj_iff ω a.val b.val).mp hab).choose_spec
  have hEq : C = uniqueInfiniteComponent hOld :=
    (eq_uniqueInfiniteComponent_iff hOld C).mpr hC
  have huniq := finiteBondFlip_induce_existsUnique_infinite_component _ hOld hNew hopen
  rw [← hEq, singletonBondFlip_induce_eq_deleteEdges C hab] at huniq
  rw [singletonBondFlip_induce_eq_deleteEdges C hab] at hsep
  apply Network.eq_of_harmonic_unique_infinite_deleted (componentGraph C) hab huniq hsep u
  intro x
  rw [← componentLaplacian_eq_netLaplacian]
  exact hu.1.1 x

end LatticeProb.Percolation
