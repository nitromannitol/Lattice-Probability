import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact

/-! # Compact connected witnesses for non-singleton components -/

set_option autoImplicit false

open Set TopologicalSpace

namespace LatticeProb

/-- A compact set has a non-singleton component exactly when it contains a
non-singleton compact connected subset. -/
theorem exists_nonsubsingleton_component_iff_compact_connected_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] {S : Set X} (hS : IsCompact S) :
    (∃ C ∈ connectedComponentIn S '' S, ¬ C.Subsingleton) ↔
      ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ K ⊆ S ∧ ¬ K.Subsingleton := by
  constructor
  · rintro ⟨C, ⟨x, hx, rfl⟩, hn⟩
    have hc : IsClosed (connectedComponentIn S x) := by
      apply closure_subset_iff_isClosed.mp
      apply IsPreconnected.subset_connectedComponentIn
        isPreconnected_connectedComponentIn.closure
      · exact subset_closure (mem_connectedComponentIn hx)
      · exact closure_minimal (connectedComponentIn_subset S x) hS.isClosed
    exact ⟨_, hS.of_isClosed_subset hc (connectedComponentIn_subset S x),
      (isConnected_connectedComponentIn_iff.mpr hx), connectedComponentIn_subset S x, hn⟩
  · rintro ⟨K, _, hK, hKS, hn⟩
    obtain ⟨x, hx⟩ := hK.nonempty
    have hxS := hKS hx
    have hsub := hK.isPreconnected.subset_connectedComponentIn hx hKS
    refine ⟨connectedComponentIn S x, ⟨x, hxS, rfl⟩, ?_⟩
    intro hs
    exact hn (hs.anti hsub)

end LatticeProb
