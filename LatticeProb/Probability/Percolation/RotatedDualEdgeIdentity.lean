import LatticeProb.Probability.Percolation.RotatedDualWalkSubdivision
import LatticeProb.Probability.Percolation.WalkSubdivisionDisjoint

/-!
# Separating edges of rotated dual steps

A collision of a rotated dual midpoint with a primal edge midpoint identifies the
rotated primal edge with the separating edge of the dual step.
-/

namespace Percolation.Literature

open SimpleGraph

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

/-- The exposure rotation sends a colliding primal edge to the separating edge. -/
theorem rotated_edge_eq_sepEdge (n : ℕ) {f g x y : V}
    (hfg : G.Adj f g) (hxy : G.Adj x y)
    (hmid : rotatedFaceMidpoint n f g = x + y) :
    s(((reflX n).trans transposeIso) x, ((reflX n).trans transposeIso) y) = sepEdge f g := by
  let R : G ≃g G := (reflX n).trans transposeIso
  have hR : G.Adj (R x) (R y) := R.map_adj_iff.mpr hxy
  have hsep : G.Adj (sepLo f g) (sepHi f g) := by
    exact G.mem_edgeSet.mp (sepEdge_mem_edgeSet hfg)
  apply (edgeMidpoint_eq_iff hR hsep).mp
  have h0 := congrFun hmid 0
  have h1 := congrFun hmid 1
  simp only [rotatedFaceMidpoint, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply] at h0 h1
  have hsum : sepLo f g + sepHi f g =
      ![f 0 + g 0 + 1, f 1 + g 1 + 1] := by
    rcases stepKind_of_adj hfg with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · have hg : g = f + Pi.single 0 1 := by
        rw [LatticeModels.Site.eq_iff_two]; simp [a, b]
      rw [hg, sepLo_add_e0, sepHi_add_e0]
      ext i; fin_cases i <;> simp <;> omega
    · have hf : f = g + Pi.single 0 1 := by
        rw [LatticeModels.Site.eq_iff_two]; simp [a, b]
      rw [sepLo_comm, sepHi_comm, hf, sepLo_add_e0, sepHi_add_e0]
      ext i; fin_cases i <;> simp <;> omega
    · have hg : g = f + Pi.single 1 1 := by
        rw [LatticeModels.Site.eq_iff_two]; simp [a, b]
      rw [hg, sepLo_add_e1, sepHi_add_e1]
      ext i; fin_cases i <;> simp <;> omega
    · have hf : f = g + Pi.single 1 1 := by
        rw [LatticeModels.Site.eq_iff_two]; simp [a, b]
      rw [sepLo_comm, sepHi_comm, hf, sepLo_add_e1, sepHi_add_e1]
      ext i; fin_cases i <;> simp <;> omega
  have hs0 := congrFun hsum 0
  have hs1 := congrFun hsum 1
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hs0 hs1
  ext i
  fin_cases i <;>
    simp [R, RelIso.trans_apply] <;> omega

end
end Percolation.Literature
