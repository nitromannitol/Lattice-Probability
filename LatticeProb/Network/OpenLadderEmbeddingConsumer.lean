import LatticeProb.Network.OpenLadderEmbedding

/-!
# Concrete ambient open-ladder examples

The two- and three-dimensional realizations exhibit genuine edges and absent edges at heights
one and two. An explicit out-of-plane unit step leaves the open carrier in dimension three.
-/

namespace LatticeProb.Network.OpenLadder.Embedding.Consumer

open LatticeProb.Percolation

/-- At height one in dimension two the terminal is adjacent to the first left rung. -/
theorem two_one_source_edge :
    (ambientGraph (d := 2) (by omega) 1).Adj
      (ambientEquiv (by omega) 1 (source 1))
      (ambientEquiv (by omega) 1 (left 1 1 ⟨by omega, by omega⟩)) := by
  apply (ambient_adj_iff (by omega) _ _).mpr
  change (1 = 2 ∧ _) ∨ (1 = 1 ∧ (1 + 1 = 2 ∨ 2 + 1 = 1))
  omega

/-- At height two in dimension two there is no edge directly between the terminal leaves. -/
theorem two_two_terminals_not_adjacent :
    ¬ (nearestNeighborGraph 2).Adj
      (ambientMap (by omega) (source 2)) (ambientMap (by omega) (target 2)) := by
  rw [ambient_adj_iff]
  change ¬ ((1 = 4 ∧ _) ∨ (1 = 1 ∧ (1 + 1 = 4 ∨ 4 + 1 = 1)))
  omega

/-- At height one in dimension three even the terminal's extra coordinate is exactly zero. -/
theorem three_one_source_extra_zero :
    ambientMap (d := 3) (by omega) (source 1) ⟨2, by omega⟩ = 0 :=
  zeroPad_extra (source 1).val (2 : Fin 3) (by decide)

/-- At height two in dimension three the left column has its genuine vertical edge. -/
theorem three_two_vertical_edge :
    (ambientGraph (d := 3) (by omega) 2).Adj
      (ambientIso (by omega) 2 (left 2 1 ⟨by omega, by omega⟩))
      (ambientIso (by omega) 2 (left 2 2 ⟨by omega, by omega⟩)) := by
  apply (ambient_adj_iff (by omega) _ _).mpr
  change (2 = 2 ∧ (1 + 1 = 2 ∨ 2 + 1 = 1)) ∨ _
  omega

/-- A third-coordinate unit step from the source is a lattice neighbor outside the open gadget. -/
theorem three_two_offplane_neighbor :
    (nearestNeighborGraph 3).Adj (ambientMap (by omega) (source 2))
        (ambientMap (by omega) (source 2) + LatticeProb.unit (2 : Fin 3)) ∧
      ambientMap (by omega) (source 2) + LatticeProb.unit (2 : Fin 3) ∉
        ambientSites (by omega) 2 := by
  constructor
  · exact ⟨2, Or.inl rfl⟩
  · intro h
    have hz := h.2 (2 : Fin 3) (by omega)
    norm_num [ambientMap, zeroPad, LatticeProb.unit, Pi.single_apply] at hz

end LatticeProb.Network.OpenLadder.Embedding.Consumer
