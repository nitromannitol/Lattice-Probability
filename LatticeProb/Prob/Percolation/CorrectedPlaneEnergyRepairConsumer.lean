import LatticeProb.Prob.Percolation.CorrectedPlaneEnergyRepair
import LatticeProb.Prob.Percolation.DeletedInfiniteComponentConsumer

/-!
# Nonzero forcing in the fully open horizontal deletion

The coordinate plane has drop one from the horizontal endpoint to the origin. Its
Laplacian on the true deleted carrier equals one at that endpoint. The constructed
same-slope plane is harmonic there and differs by a bounded finite-energy function.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Classical

namespace LatticeProb.Percolation.HorizontalDeletionRepair

open LatticeProb.Graph LatticeProb.Graph.Zd

noncomputable section

local notation "C" => uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)

/-- The actual old component vertex at the lattice origin. -/
def origin : C := ⟨0, by
  change (0 : Vertex 2) ∈ (C).supp
  rw [uniqueInfiniteComponent_allOpen_supp]
  trivial⟩

/-- The actual old component vertex one horizontal unit from the origin. -/
def horizontalEndpoint : C := ⟨unit (0 : Fin 2), by
  change unit (0 : Fin 2) ∈ (C).supp
  rw [uniqueInfiniteComponent_allOpen_supp]
  trivial⟩

/-- The directed component edge is oriented to give coordinate drop positive one. -/
theorem horizontal_adj : (componentGraph C).Adj horizontalEndpoint origin := by
  change (openGraph (allOpen 2)).Adj (unit (0 : Fin 2)) 0
  rw [openGraph_allOpen]
  exact (show (nearestNeighborGraph 2).Adj 0 (unit (0 : Fin 2)) from
    ⟨0, Or.inl (zero_add _).symm⟩).symm

/-- The canonical bond from the actual component edge is the horizontal unit bond. -/
theorem componentEdgeBond_eq_horizontal :
    componentEdgeBond C horizontal_adj = horizontalUnitBond := by
  apply Subtype.ext
  exact Sym2.eq_swap

/-- This actual component-edge flip is exactly the accepted horizontal singleton flip. -/
theorem componentEdgeFlip_eq_horizontal :
    componentEdgeFlip C horizontal_adj = finiteBondFlip {horizontalUnitBond} (allOpen 2) := by
  rw [componentEdgeFlip, componentEdgeBond_eq_horizontal]

/-- The selected new component exists uniquely on this explicit configuration. -/
theorem flipped_unique : HasUniqueInfiniteOpenComponent (componentEdgeFlip C horizontal_adj) := by
  rw [componentEdgeFlip_eq_horizontal]
  exact allOpen_flip_horizontal_hasUniqueInfiniteOpenComponent

/-- The square detour supplies actual reachability on the full old carrier. -/
theorem flipped_reachable :
    ((openGraph (componentEdgeFlip C horizontal_adj)).induce (C).supp).Reachable
      horizontalEndpoint origin := by
  rw [componentEdgeFlip_eq_horizontal]
  apply (Graph.reachable_induce_component_iff
    (openGraph_finiteBondFlip_le_of_all_open {horizontalUnitBond} (allOpen 2)
      (fun _ _ => rfl)) C horizontalEndpoint origin).mpr
  exact allOpen_flip_horizontal_detour.symm

/-- The original coordinate drop across the removed edge is exactly positive one. -/
theorem coordinate_drop :
    (horizontalEndpoint.val 0 : ℝ) - (origin.val 0 : ℝ) = 1 := by
  norm_num [horizontalEndpoint, origin, unit, Pi.single_apply]

/-- The old coordinate plane has nonzero forcing on the literal deleted graph. -/
theorem deleted_coordinate_laplacian_endpoint :
    laplacian ((componentGraph C).deleteEdges
      (({s(horizontalEndpoint, origin)} : Finset (Sym2 C)) : Set (Sym2 C)))
      (fun x : C => (x.val 0 : ℝ)) horizontalEndpoint = 1 := by
  rw [Network.laplacian_delete_singleton_of_harmonic (componentGraph C) horizontal_adj
    (fun x : C => (x.val 0 : ℝ)) (allOpen_component_coordinate_harmonic 2 0),
    coordinate_drop, if_pos rfl, if_neg horizontal_adj.ne]
  ring

/-- The actual new plane has the original nonzero coordinate slope, is harmonic on the
true new component, and has bounded finite-energy difference from the old coordinate.
Its pullback cannot equal the original coordinate plane because that has forcing one. -/
theorem exists_coordinate_repair :
    let E := nonBridgeComponentEquiv C (allOpen_hasUniqueInfiniteOpenComponent 2)
      (uniqueInfiniteComponent_infinite (allOpen_hasUniqueInfiniteOpenComponent 2))
      horizontal_adj flipped_unique flipped_reachable
    ∃ v : uniqueInfiniteComponent flipped_unique → ℝ, ∃ B K : ℝ,
      IsCorrectedPlane (uniqueInfiniteComponent flipped_unique) (Pi.single 0 1) v ∧
      (∀ y, |v y - ((E.symm y).val 0 : ℝ)| ≤ B) ∧
      (∀ F : Finset (uniqueInfiniteComponent flipped_unique ×
          uniqueInfiniteComponent flipped_unique),
        (∀ e ∈ F, (componentGraph (uniqueInfiniteComponent flipped_unique)).Adj e.1 e.2) →
        ∑ e ∈ F, ((v e.1 - ((E.symm e.1).val 0 : ℝ)) -
          (v e.2 - ((E.symm e.2).val 0 : ℝ))) ^ 2 ≤ K) ∧
      ¬ (∀ x : C, v (E x) = (x.val 0 : ℝ)) := by
  let E := nonBridgeComponentEquiv C (allOpen_hasUniqueInfiniteOpenComponent 2)
    (uniqueInfiniteComponent_infinite (allOpen_hasUniqueInfiniteOpenComponent 2))
    horizontal_adj flipped_unique flipped_reachable
  obtain ⟨v, B, K, hv, hB, hK⟩ :=
    exists_correctedPlane_bounded_finite_energy_of_nonbridge C
      (allOpen_hasUniqueInfiniteOpenComponent 2)
      (uniqueInfiniteComponent_infinite (allOpen_hasUniqueInfiniteOpenComponent 2))
      horizontal_adj flipped_unique flipped_reachable (allOpen_isCorrectedPlane_coordinate 2 0)
  refine ⟨v, B, K, hv, hB, hK, ?_⟩
  intro heq
  change ∀ x : C, v (E x) = (x.val 0 : ℝ) at heq
  have hvfun : v = fun y => ((E.symm y).val 0 : ℝ) := by
    funext y
    have hy := heq (E.symm y)
    rw [E.apply_symm_apply] at hy
    exact hy
  have hh := hv.1.1 (E horizontalEndpoint)
  rw [hvfun] at hh
  have ht := nonBridgeComponent_laplacian C (allOpen_hasUniqueInfiniteOpenComponent 2)
    (uniqueInfiniteComponent_infinite (allOpen_hasUniqueInfiniteOpenComponent 2))
    horizontal_adj flipped_unique flipped_reachable
    (fun x : C => (x.val 0 : ℝ)) horizontalEndpoint
  rw [deleted_coordinate_laplacian_endpoint] at ht
  change componentLaplacian (uniqueInfiniteComponent flipped_unique)
    (fun y => ((E.symm y).val 0 : ℝ)) (E horizontalEndpoint) = 1 at ht
  linarith

end

end LatticeProb.Percolation.HorizontalDeletionRepair
