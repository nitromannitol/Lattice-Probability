import LatticeProb.Bonanno.ReflectedGMS.GMS.LineConnectedPoint
import LatticeProb.Prob.CellConfigWalkMeasurable
import LatticeProb.Prob.DyadicCellMass
import LatticeProb.Walk.CellConfigSRWChain
import LatticeProb.Walk.ConnectedChainInfiniteRange

/-! # Infinite range of a walk on a line-connected cell configuration -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open ReflectedGMS ReflectedGMS.GMS
open scoped ENNReal

namespace LatticeProb.CellConfigWalk

/-- Connectedness along lines implies connectedness of the full cell graph. -/
theorem graph_connected_of_lineConnected (H : CellConfig) (hH : H.IsCellConfiguration)
    (hL : H.LineConnected) : H.graph.Connected := by
  have hpre : H.graph.Preconnected := by
    intro K K'
    obtain ⟨x, hx⟩ := K.1.nonempty
    obtain ⟨y, hy⟩ := K'.1.nonempty
    let B : Set Plane := Metric.closedBall x (dist x y)
    have hxB : x ∈ B := by simp [B]
    have hyB : y ∈ B := by simp [B, dist_comm]
    have hB : IsConnected B :=
      (convex_closedBall x (dist x y)).isConnected ⟨x, hxB⟩
    have hconn := CellConfig.inducedGraph_connected_of_isCompact hH
      (fun z => (CellConfig.inducedGraph_singleton_connected_of_lineConnected hH hL z).preconnected)
      (isCompact_closedBall x (dist x y)) hB
    have hpath := hconn.preconnected ⟨K, x, hx, hxB⟩ ⟨K', y, hy, hyB⟩
    exact hpath.map (SimpleGraph.Embedding.induce _).toHom
  have hne : Nonempty H.cells := by
    have h := hH.iUnion_eq_univ
    have h0 : (0 : Plane) ∈ ⋃ K ∈ H.cells, (K : Set Plane) := by rw [h]; exact mem_univ _
    obtain ⟨K, hK, _⟩ := mem_iUnion₂.1 h0
    exact ⟨⟨K, hK⟩⟩
  exact (SimpleGraph.connected_iff _).2 ⟨hpre, hne⟩

/-- Any simple random walk law on a line-connected cell configuration visits
infinitely many cells almost surely. -/
theorem ae_infinite_range_of_lineConnected (H : CellConfig) (hH : H.IsCellConfiguration)
    (hL : H.LineConnected) {K : H.cells} {Q : Measure (ℕ → H.cells)}
    (hQ : H.IsSRWLaw K Q) : ∀ᵐ ω ∂Q, (Set.range ω).Infinite := by
  let : Countable H.cells := countable_cells_of_locallyFinite hH.locallyFinite
  let : Infinite H.cells := CellMass.infinite_of_iUnion_eq_univ
    (by simpa only [iUnion_subtype] using hH.iUnion_eq_univ) (fun K => K.1.isCompact)
  let : IsMarkovKernel (CellConfigSRW.kernel H) := CellConfigSRW.isMarkovKernel_kernel H hH
  rw [CellConfigSRW.eq_walkLaw_of_isSRWLaw H hH hQ]
  apply chainLaw_ae_infinite_range (CellConfigSRW.kernel H) H.graph
    (graph_connected_of_lineConnected H hH hL) ?_ K
  intro x y hxy
  have hc : 0 < H.c x y := hxy.2.1
  have hpi : 0 < H.pi x := pi_pos_of_adj hH hc
  rw [CellConfigSRW.kernel_singleton H hpi y]
  exact ENNReal.ofReal_pos.mpr (div_pos hc hpi)

end LatticeProb.CellConfigWalk
end
