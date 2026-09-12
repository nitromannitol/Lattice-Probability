/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Dual

open Fin.NatCast

namespace LatticeProb.Lattice.Planar

theorem leftFace_eq (v : Site) (a : Dir) : leftFace v a = rightFace v (a - 1) := by
  fin_cases a
  · simp [leftFace, rightFace, dirVec]; omega
  all_goals simp [leftFace, rightFace, dirVec]

theorem adj_rightFace_leftFace (v : Site) (a : Dir) :
    squareGraph.Adj (rightFace v a) (leftFace v a) := by
  rw [squareGraph_adj]
  fin_cases a <;> simp [leftFace, rightFace, dirVec]

theorem primalTail_dual (v : Site) (a : Dir) : primalTail (rightFace v a) (leftFace v a) = v := by
  obtain ⟨x, y⟩ := v
  fin_cases a <;> simp [primalTail, leftFace, rightFace, dirVec]

theorem primalDir_dual (v : Site) (a : Dir) : primalDir (rightFace v a) (leftFace v a) = a := by
  obtain ⟨x, y⟩ := v
  fin_cases a <;> simp [primalDir, leftFace, rightFace, dirVec, dirOf]

/-- The face on the right of `p → v` is the face on the right of the edge out of `v` one step
clockwise before the reverse edge `v → p`. -/
theorem rightFace_rev {p v : Site} (h : squareGraph.Adj p v) :
    rightFace p (dirOf (v - p)) = rightFace v (dirOf (p - v) - 1) := by
  have hv : v = p + dirVec (dirOf (v - p)) := (dirVec_dirOf_of_adj h).symm
  generalize dirOf (v - p) = a at hv
  subst hv
  obtain ⟨x, y⟩ := p
  fin_cases a <;> simp [rightFace, dirVec, dirOf]

/-- The faces `rightFace v c, rightFace v (c-1), …, rightFace v (c-n)`. -/
def faces (v : Site) (c : Dir) : ℕ → List Site
  | 0 => [rightFace v c]
  | n + 1 => rightFace v c :: faces v (c - 1) n

theorem faces_head (v : Site) (c : Dir) (n : ℕ) : (faces v c n).head? = some (rightFace v c) := by
  cases n <;> rfl

theorem faces_ne_nil (v : Site) (c : Dir) (n : ℕ) : faces v c n ≠ [] := by
  cases n <;> simp [faces]

theorem faces_getLast (v : Site) (c : Dir) : ∀ n : ℕ,
    (faces v c n).getLast (faces_ne_nil v c n) = rightFace v (c - (n : Dir))
  | 0 => by simp [faces]
  | n + 1 => by
    show (rightFace v c :: faces v (c - 1) n).getLast _ = _
    rw [List.getLast_cons (faces_ne_nil v (c - 1) n), faces_getLast]
    congr 1
    apply Fin.ext
    simp only [Fin.val_sub, Fin.val_natCast, Fin.val_one]
    omega

theorem faces_getLast? (v : Site) (c : Dir) (n : ℕ) :
    (faces v c n).getLast? = some (rightFace v (c - (n : Dir))) := by
  rw [List.getLast?_eq_some_getLast (faces_ne_nil v c n), faces_getLast]

end LatticeProb.Lattice.Planar
