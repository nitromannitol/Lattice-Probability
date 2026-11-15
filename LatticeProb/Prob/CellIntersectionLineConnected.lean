import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedPoint

/-! # Connectivity for intersection-adjacent cell configurations -/

set_option autoImplicit false

open Set

namespace ReflectedGMS.GMS.CellConfig

/-- If intersecting distinct cells are adjacent, the cells meeting any compact connected
set form a connected graph. -/
theorem inducedGraph_connected_of_intersections {H : CellConfig}
    (hH : H.IsCellConfiguration)
    (hadj : ∀ K ∈ H.cells, ∀ K' ∈ H.cells, K ≠ K' →
      ((K : Set Plane) ∩ K').Nonempty → H.Adj K K')
    {L : Set Plane} (hLc : IsCompact L) (hL : IsConnected L) :
    (H.inducedGraph L).Connected := by
  apply inducedGraph_connected_of_isCompact hH ?_ hLc hL
  intro z u v
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    have hne : (u.1 : Cell) ≠ (v.1 : Cell) := by
      intro heq
      apply huv
      apply Subtype.ext
      exact Subtype.ext heq
    have hzU : z ∈ ((u.1 : Cell) : Set Plane) := Set.inter_singleton_nonempty.mp u.2
    have hzV : z ∈ ((v.1 : Cell) : Set Plane) := Set.inter_singleton_nonempty.mp v.2
    change u.1 ≠ v.1 ∧ H.Adj u.1 v.1 ∧ H.Adj v.1 u.1
    exact ⟨fun h => hne (congrArg Subtype.val h),
      hadj u.1 u.1.2 v.1 v.1.2 hne ⟨z, hzU, hzV⟩,
      hadj v.1 v.1.2 u.1 u.1.2 hne.symm ⟨z, hzV, hzU⟩⟩

/-- If intersecting distinct cells are adjacent, the configuration is connected along lines. -/
theorem lineConnected_of_intersections {H : CellConfig}
    (hH : H.IsCellConfiguration)
    (hadj : ∀ K ∈ H.cells, ∀ K' ∈ H.cells, K ≠ K' →
      ((K : Set Plane) ∩ K').Nonempty → H.Adj K K') : H.LineConnected := by
  apply (lineConnected_iff_forall_singleton hH).2
  intro z
  exact inducedGraph_connected_of_intersections hH hadj isCompact_singleton isConnected_singleton

end ReflectedGMS.GMS.CellConfig
