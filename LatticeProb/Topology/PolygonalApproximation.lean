module

/-
# Separated polygonal connections near compact continua

The connections are constructed in disjoint connected open neighborhoods.
The continua themselves need only be topologically connected.
-/
public import LatticeProb.Topology.PolygonalChain
public import LatticeProb.Topology.ConnectedThickening

@[expose] public section



open Metric Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Separated polygonal connections.** Prescribed pairs of points of disjoint compact continua admit disjoint finite
polygonal connections inside any prescribed open neighborhoods. The returned
single-radius thickenings retain quantitative locality for later endpoint extensions. -/
theorem exists_disjoint_polygonal_chains {K L U V : Set E}
    (hK : IsCompact K) (hKc : IsConnected K)
    (hL : IsCompact L) (hLc : IsConnected L) (hKL : Disjoint K L)
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hLV : L ⊆ V)
    {a b c d : E} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ L) (hd : d ∈ L) :
    ∃ r > 0, ∃ vs ws : List E, ∃ hv : vs ≠ [], ∃ hw : ws ≠ [],
      vs.head hv = a ∧ vs.getLast hv = b ∧ ws.head hw = c ∧ ws.getLast hw = d ∧
      polygonalChain vs ⊆ thickening r K ∧ polygonalChain ws ⊆ thickening r L ∧
      thickening r K ⊆ U ∧ thickening r L ⊆ V ∧
      Disjoint (thickening r K) (thickening r L) ∧
      Disjoint (polygonalChain vs) (polygonalChain ws) := by
  obtain ⟨r, hr, hsep, hKr, hLr, hKo, hLo, hKrc, hLrc⟩ :=
    exists_disjoint_connected_open_thickenings hK hKc hL hLc hKL hU hV hKU hLV
  obtain ⟨vs, hv, hvs, hhead, hlast⟩ := exists_polygonal_chain_of_isPreconnected hKo
    hKrc.isPreconnected (self_subset_thickening hr K ha) (self_subset_thickening hr K hb)
  obtain ⟨ws, hw, hws, whead, wlast⟩ := exists_polygonal_chain_of_isPreconnected hLo
    hLrc.isPreconnected (self_subset_thickening hr L hc) (self_subset_thickening hr L hd)
  exact ⟨r, hr, vs, ws, hv, hw, hhead, hlast, whead, wlast,
    hvs, hws, hKr, hLr, hsep, hsep.mono hvs hws⟩

end LatticeProb.Topology
