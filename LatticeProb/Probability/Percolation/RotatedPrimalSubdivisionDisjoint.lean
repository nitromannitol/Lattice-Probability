import LatticeProb.Probability.Percolation.RotatedDualWalkSubdivision
import LatticeProb.Probability.Percolation.WalkSubdivision

/-!
# Disjointness of primal and rotated dual subdivisions

If no primal edge midpoint coincides with a rotated dual edge midpoint, the corresponding
subdivided walks have disjoint supports.
-/

namespace Percolation.Literature

open SimpleGraph

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

/-- A rotated dual edge midpoint is not a doubled lattice vertex. -/
theorem rotatedFaceMidpoint_ne_double (n : ℕ) {f g : V} (hfg : G.Adj f g) (v : V) :
    rotatedFaceMidpoint n f g ≠ v + v := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [rotatedFaceMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply] at h0 h1
  rcases stepKind_of_adj hfg with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega

/-- Subdivided primal and rotated dual walks are disjoint when their edge midpoints differ. -/
theorem disjoint_support_subdivideWalk_rotatedDual (n : ℕ) {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d)
    (h : ∀ x y, s(x, y) ∈ p.edges → ∀ f g, s(f, g) ∈ q.edges →
      x + y ≠ rotatedFaceMidpoint n f g) :
    Disjoint {z | z ∈ (subdivideWalk p).support}
      {z | z ∈ (subdivideRotatedDualWalk n q).support} := by
  apply Set.disjoint_left.mpr
  intro z hp hq
  rcases (mem_support_subdivideWalk p).mp hp with ⟨x, hx, hzx⟩ | ⟨x, y, hxy, hzx⟩ <;>
    rcases (mem_support_subdivideRotatedDualWalk n q).mp hq with
      ⟨f, hf, hzf⟩ | ⟨f, g, hfg, hzf⟩
  · exact rotatedFaceCenter_ne_double n f x (hzf.symm.trans hzx)
  · exact rotatedFaceMidpoint_ne_double n (q.adj_of_mem_edges hfg) x (hzf.symm.trans hzx)
  · exact rotatedFaceCenter_ne_edgeMidpoint n f x y (p.adj_of_mem_edges hxy)
      (hzf.symm.trans hzx)
  · exact h x y hxy f g hfg (hzx.symm.trans hzf)

end

end Percolation.Literature
