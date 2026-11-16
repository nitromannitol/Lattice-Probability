import LatticeProb.Probability.Percolation.RotatedDualWalkSubdivision
import LatticeProb.Probability.Percolation.WalkSubdivisionDisjoint

/-!
# Support of a rotated face-corner connection

A two-step connection from a face corner to the rotated face center stays inside the doubled
face and avoids a subdivided walk whenever the original walk avoids the corner.
-/

namespace Percolation.Literature

open SimpleGraph

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

/-- The corner connection stays in the doubled physical face. -/
theorem rotatedFaceCornerWalk_bounds (n : ℕ) (f v : V)
    (hx : v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1)
    (hy : v 1 = f 0 ∨ v 1 = f 0 + 1) :
    ∀ z ∈ (rotatedFaceCornerWalk n f v hx hy).support,
      2 * ((n : ℤ) - f 1 - 1) ≤ z 0 ∧
      z 0 ≤ 2 * ((n : ℤ) - f 1 - 1) + 2 ∧
      2 * f 0 ≤ z 1 ∧ z 1 ≤ 2 * f 0 + 2 := by
  intro z hz
  rcases (mem_support_rotatedFaceCornerWalk n f v z hx hy).mp hz with rfl | rfl | rfl
  · simp only [Pi.add_apply]; omega
  · simp only [rotatedFaceCornerMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  · simp only [rotatedFaceCenter, Matrix.cons_val_zero, Matrix.cons_val_one]; omega

/-- Bounds when the face index lies in the rectangle below the top row. -/
theorem rotatedFaceCornerWalk_bounds_of_index (n : ℕ) (f v : V)
    (hx : v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1)
    (hy : v 1 = f 0 ∨ v 1 = f 0 + 1)
    (hf : 0 ≤ f 0 ∧ f 0 ≤ (n : ℤ) - 1 ∧
      -1 ≤ f 1 ∧ f 1 ≤ (n : ℤ) - 1) :
    ∀ z ∈ (rotatedFaceCornerWalk n f v hx hy).support,
      0 ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 2 ∧
      0 ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
  intro z hz
  have h := rotatedFaceCornerWalk_bounds n f v hx hy z hz
  omega

/-- A face-corner connection avoids the subdivision of a walk that avoids the corner. -/
theorem disjoint_support_rotatedFaceCornerWalk_subdivideWalk (n : ℕ) (f v : V)
    (hx : v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1)
    (hy : v 1 = f 0 ∨ v 1 = f 0 + 1)
    {a b : V} (p : G.Walk a b) (hv : v ∉ p.support) :
    Disjoint {z | z ∈ (rotatedFaceCornerWalk n f v hx hy).support}
      {z | z ∈ (subdivideWalk p).support} := by
  apply Set.disjoint_left.mpr
  intro z hz hp
  rcases (mem_support_rotatedFaceCornerWalk n f v z hx hy).mp hz with rfl | rfl | rfl
  · rcases (mem_support_subdivideWalk p).mp hp with ⟨x, hxp, heq⟩ | ⟨x, y, he, heq⟩
    · have hvx : v = x := by
        apply funext
        intro i
        have hi := congrFun heq i
        simp only [Pi.add_apply] at hi
        omega
      exact hv (hvx ▸ hxp)
    · exact double_ne_edgeMidpoint v (p.adj_of_mem_edges he) heq
  · obtain ⟨w, hvw, _, _, hm⟩ := rotatedFaceCornerMidpoint_eq_edgeMidpoint n f v hx
    rcases (mem_support_subdivideWalk p).mp hp with ⟨x, _, heq⟩ | ⟨x, y, he, heq⟩
    · exact double_ne_edgeMidpoint x hvw (heq.symm.trans hm)
    · have h : v = x ∨ v = y := endpoint_eq_of_edgeMidpoint_eq hvw
        (p.adj_of_mem_edges he) (hm.symm.trans heq)
      rcases h with rfl | rfl
      · exact hv (p.fst_mem_support_of_mem_edges he)
      · exact hv (p.snd_mem_support_of_mem_edges he)
  · rcases (mem_support_subdivideWalk p).mp hp with ⟨x, _, heq⟩ | ⟨x, y, he, heq⟩
    · exact rotatedFaceCenter_ne_double n f x heq
    · exact rotatedFaceCenter_ne_edgeMidpoint n f x y (p.adj_of_mem_edges he) heq

end

end Percolation.Literature
