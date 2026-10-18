/-
Translation invariance of the nearest-neighbour adjacency of `ℤ^d`: adding one
fixed site to both endpoints of a pair of sites preserves adjacency in
`LatticeProb.lattice d`, and conversely.  The statement depends only on the
definition of `LatticeProb.lattice` and `LatticeProb.unit` in `LatticeProb.Site`.
-/
import Mathlib
import LatticeProb.Site

namespace LatticeProb

/-- Nearest-neighbour adjacency is invariant under translation. -/
theorem lattice_adj_add_right_iff {d : ℕ} (c x y : Site d) :
    (lattice d).Adj (x + c) (y + c) ↔ (lattice d).Adj x y := by
  show (∃ i : Fin d, y + c = x + c + unit i ∨ x + c = y + c + unit i) ↔
    ∃ i : Fin d, y = x + unit i ∨ x = y + unit i
  refine exists_congr fun i => or_congr ?_ ?_
  · rw [add_right_comm x c (unit i), add_left_inj]
  · rw [add_right_comm y c (unit i), add_left_inj]

end LatticeProb
