import LatticeProb.Probability.Percolation.RotatedDualWalkSubdivision
import LatticeProb.Probability.Percolation.WalkSubdivision

/-!
# The right endpoint of a rotated dual walk

A bottom-side face center is joined to the right boundary by one lattice step. Its
support lies in the crossing rectangle and avoids a subdivided walk to its left.
-/

namespace Percolation.Literature

open SimpleGraph

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

/-- The final step from a rotated bottom-side face center to the right boundary. -/
def rotatedDualEndpointWalk (n : ℕ) {b : V} (hb : b ∈ dualBottomSide n n) :
    G.Walk (rotatedFaceCenter n b) (rotatedDualEndpoint n b) :=
  .cons (adj_rotatedFaceCenter_endpoint n hb) .nil

/-- The support of the final step consists of its two endpoints. -/
theorem mem_support_rotatedDualEndpointWalk (n : ℕ) {b z : V}
    (hb : b ∈ dualBottomSide n n) :
    z ∈ (rotatedDualEndpointWalk n hb).support ↔
      z = rotatedFaceCenter n b ∨ z = rotatedDualEndpoint n b := by
  simp [rotatedDualEndpointWalk]

/-- Every point of the final step lies in the crossing rectangle, strictly to the right
of the doubled primal square. -/
theorem rotatedDualEndpointWalk_bounds (n : ℕ) (hn : 1 ≤ n) {b : V}
    (hb : b ∈ dualBottomSide n n) :
    ∀ z ∈ (rotatedDualEndpointWalk n hb).support,
      -2 * (n : ℤ) ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 2 ∧
      -2 * (n : ℤ) ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) ∧ 2 * (n : ℤ) < z 0 := by
  intro z hz
  rcases (mem_support_rotatedDualEndpointWalk n hb).mp hz with rfl | rfl
  all_goals
    have h := rotatedDualEndpoint_bounds n hb
    have hc := (rotatedFaceCenter_of_mem_dualBottomSide n hb).1
    simp only [hc, rotatedDualEndpoint, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
    omega

/-- Appending the final step adds precisely its endpoint to the subdivided dual support. -/
theorem mem_support_subdivideRotatedDualWalk_append_endpoint (n : ℕ) {a b z : V}
    (p : G.Walk a b) (hb : b ∈ dualBottomSide n n) :
    z ∈ ((subdivideRotatedDualWalk n p).append (rotatedDualEndpointWalk n hb)).support ↔
      z ∈ (subdivideRotatedDualWalk n p).support ∨ z = rotatedDualEndpoint n b := by
  rw [Walk.mem_support_append_iff, mem_support_rotatedDualEndpointWalk]
  have hc := (subdivideRotatedDualWalk n p).end_mem_support
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · subst z; exact Or.inl hc
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- The endpoint step avoids the subdivision of any walk confined to the primal square's
right half-plane bound. -/
theorem disjoint_support_rotatedDualEndpointWalk_subdivideWalk (n : ℕ) (hn : 1 ≤ n)
    {a b c : V} (hb : b ∈ dualBottomSide n n) (p : G.Walk a c)
    (hp : ∀ x ∈ p.support, x 0 ≤ (n : ℤ)) :
    Disjoint {z | z ∈ (rotatedDualEndpointWalk n hb).support}
      {z | z ∈ (subdivideWalk p).support} := by
  apply Set.disjoint_left.mpr
  intro z hz hzp
  have hz' := (rotatedDualEndpointWalk_bounds n hn hb z hz).2.2.2.2
  rcases (mem_support_subdivideWalk p).mp hzp with ⟨x, hx, rfl⟩ | ⟨x, y, he, rfl⟩
  · have hx' := hp x hx
    simp only [Pi.add_apply] at hz'
    omega
  · have hx := hp x (p.fst_mem_support_of_mem_edges he)
    have hy := hp y (p.snd_mem_support_of_mem_edges he)
    simp only [Pi.add_apply] at hz'
    omega

end
end Percolation.Literature
