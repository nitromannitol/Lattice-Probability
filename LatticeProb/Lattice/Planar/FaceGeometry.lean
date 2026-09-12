/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.ContourCases

open Finset Classical Fin.NatCast

namespace LatticeProb.Lattice.Planar

theorem dualEdge_E : dualEdge (0, 0) 1 = ((0, -1), (0, 0)) := by decide

theorem dualEdge_N : dualEdge (0, 0) 0 = ((0, 0), (-1, 0)) := by decide

theorem dualEdge_W : dualEdge (0, 0) 3 = ((-1, 0), (-1, -1)) := by decide

theorem dualEdge_S : dualEdge (0, 0) 2 = ((-1, -1), (0, -1)) := by decide

/-- Every dual edge is the rotation of exactly the primal edge that
`primalTail`/`primalDir` recover. -/
theorem primal_of_dualEdge : ∀ a : Dir,
    primalTail (dualEdge (0, 0) a).1 (dualEdge (0, 0) a).2 = (0, 0) ∧
    primalDir (dualEdge (0, 0) a).1 (dualEdge (0, 0) a).2 = a := by decide

/-- With the east side as the current edge, `sideW` is the west side. -/
theorem sideW_of_E : sideW (0, -1) (0, 0) = ((-1, 0), (-1, -1)) := by decide

/-- With the east side as the current edge, `sideS` is the south side. -/
theorem sideS_of_E : sideS (0, -1) (0, 0) = ((-1, -1), (0, -1)) := by decide

/-- With the north side as the current edge, `sideW` is the south side and
`sideS` is the east side: the relabeling rotates with the current edge. -/
theorem sideW_of_N : sideW (0, 0) (-1, 0) = ((-1, -1), (0, -1)) := by decide

theorem sideS_of_N : sideS (0, 0) (-1, 0) = ((0, -1), (0, 0)) := by decide

theorem fin4_offset (a b : Fin 4) :
    b + ((((a - b).val + 3) % 4 + 1 : ℕ) : Fin 4) = a := by
  revert a b
  decide

theorem sideS_geom {t w : Site} (h : squareGraph.Adj t w) :
    sideS t w = (t + rotL (w - t), t) := by
  have h1 : w - t = rotR (rightFace (primalTail t w) (primalDir t w + 1) - t) := by
    have := corner_NE_sub_SE (primalTail t w) (primalDir t w)
    rwa [rightFace_primal h, leftFace_primal h] at this
  have hSW : rightFace (primalTail t w) (primalDir t w + 1) = t + rotL (w - t) := by
    rw [h1, rotL_rotR]; abel
  refine Prod.ext ?_ ?_
  · rw [sideS_fst, hSW]
  · rw [sideS_snd, rightFace_primal h]

theorem sideW_geom {t w : Site} (h : squareGraph.Adj t w) :
    sideW t w = (w + rotL (w - t), t + rotL (w - t)) := by
  have h1 : w - t = rotR (rightFace (primalTail t w) (primalDir t w + 1) - t) := by
    have := corner_NE_sub_SE (primalTail t w) (primalDir t w)
    rwa [rightFace_primal h, leftFace_primal h] at this
  have h2 : rightFace (primalTail t w) (primalDir t w + 2) -
      rightFace (primalTail t w) (primalDir t w + 1) = w - t := by
    have := corner_NW_sub_SW (primalTail t w) (primalDir t w)
    rwa [rightFace_primal h, leftFace_primal h] at this
  have hSW : rightFace (primalTail t w) (primalDir t w + 1) = t + rotL (w - t) := by
    rw [h1, rotL_rotR]; abel
  have hNW : rightFace (primalTail t w) (primalDir t w + 2) = w + rotL (w - t) := by
    rw [show w + rotL (w - t) = (t + rotL (w - t)) + (w - t) by abel, ← hSW, ← h2]; abel
  refine Prod.ext ?_ ?_
  · rw [sideW_fst, hNW]
  · rw [sideW_snd, hSW]

theorem rotR_rotR (u : Site) : rotR (rotR u) = -u := by
  obtain ⟨a, b⟩ := u; simp [rotR]

theorem rotL_ne_neg {u : Site} (hu : IsUnit u) : rotL u ≠ -u := by
  rcases hu with rfl | rfl | rfl | rfl <;> decide

theorem adj_of_isUnit {a b : Site} (h : IsUnit (b - a)) : squareGraph.Adj a b := adj_of_unit h

end LatticeProb.Lattice.Planar
