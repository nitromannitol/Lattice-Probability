import LatticeProb.Topology.ClopenComponentClasses
import LatticeProb.Topology.CompactPlaneComponentCardinality

/-! # Component bounds from finite-dimensional comparisons -/

open Set

namespace LatticeProb.Topology

/-- A linear embedding of reduced locally constant classes into a finite coordinate
space bounds the number of components by one more than the number of coordinates. -/
theorem cardinal_components_le_of_component_classes_embedding
    {X K B : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Field K] [Fintype B]
    (f : (LocallyConstant X K ⧸
      LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)) →ₗ[K] B → K)
    (hf : Function.Injective f) :
    Cardinal.mk (ConnectedComponents X) ≤ (Fintype.card B + 1 : ℕ) := by
  let := FiniteDimensional.of_injective f hf
  have hr := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_pi] at hr
  calc
    Cardinal.mk (ConnectedComponents X) ≤
        (Module.finrank K (LocallyConstant X K ⧸
          LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)) + 1 : ℕ) :=
      cardinal_components_le_finrank_succ
    _ ≤ (Fintype.card B + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hr 1

/-- A finite-coordinate comparison with the bounded complementary components yields the
corresponding bound on the components of a compact planar intersection. -/
theorem cardinal_inter_components_le_of_bounded_compl_embedding
    {A C : Set ℂ} {K : Type*} [Field K] (hA : IsCompact A) (hC : IsCompact C)
    [Fintype (BoundedPlaneComplementComponent (A ∪ C))]
    (f : (LocallyConstant ↥(A ∩ C) K ⧸
      LinearMap.range (LocallyConstant.constₗ K :
        K →ₗ[K] LocallyConstant ↥(A ∩ C) K)) →ₗ[K]
          BoundedPlaneComplementComponent (A ∪ C) → K)
    (hf : Function.Injective f) :
    Cardinal.mk (ConnectedComponents ↥(A ∩ C)) ≤
      (Fintype.card (BoundedPlaneComplementComponent (A ∪ C)) + 1 : ℕ) := by
  let : CompactSpace ↥(A ∩ C) := isCompact_iff_compactSpace.mp (hA.inter_right hC.isClosed)
  exact cardinal_components_le_of_component_classes_embedding f hf

end LatticeProb.Topology
