import LatticeProb.Probability.Percolation.WalkSubdivision

/-!
# Disjointness of subdivided lattice walks

Disjoint supports of square-lattice walks remain disjoint after subdivision. Equality of
edge midpoints determines the original undirected edge.
-/

namespace Percolation.Literature

open SimpleGraph

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

/-- A doubled lattice vertex is never the midpoint of a nearest-neighbor edge. -/
theorem double_ne_edgeMidpoint (z : V) {x y : V} (h : G.Adj x y) :
    z + z ≠ x + y := by
  intro heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  simp only [Pi.add_apply] at h0 h1
  rcases stepKind_of_adj h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega

/-- Two nearest-neighbor edges have the same doubled midpoint exactly when they agree. -/
theorem edgeMidpoint_eq_iff {x y u v : V} (hxy : G.Adj x y) (huv : G.Adj u v) :
    x + y = u + v ↔ s(x, y) = s(u, v) := by
  constructor
  · intro heq
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    simp only [Pi.add_apply] at h0 h1
    apply Sym2.eq_iff.mpr
    simp only [LatticeModels.Site.eq_iff_two]
    rcases stepKind_of_adj hxy with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      rcases stepKind_of_adj huv with ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ <;> omega
  · intro heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact add_comm _ _

/-- A collision with an edge midpoint identifies both endpoints of the original edge. -/
theorem endpoint_eq_of_edgeMidpoint_eq {v w x y : V} (hvw : G.Adj v w)
    (hxy : G.Adj x y) (h : v + w = x + y) : v = x ∨ v = y := by
  rcases Sym2.eq_iff.mp ((edgeMidpoint_eq_iff hvw hxy).mp h) with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Subdividing two lattice walks preserves disjointness of their original supports. -/
theorem disjoint_support_subdivideWalk {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (h : Disjoint {x | x ∈ p.support} {x | x ∈ q.support}) :
    Disjoint {x | x ∈ (subdivideWalk p).support} {x | x ∈ (subdivideWalk q).support} := by
  apply Set.disjoint_left.mpr
  intro z hp hq
  have hn := Set.disjoint_left.mp h
  rcases (mem_support_subdivideWalk p).mp hp with ⟨x, hx, hzx⟩ | ⟨x, y, hxy, hzx⟩ <;>
    rcases (mem_support_subdivideWalk q).mp hq with ⟨u, hu, hzu⟩ | ⟨u, v, huv, hzu⟩
  · have heq : x = u := by
      apply funext
      intro i
      have hi := congrFun (hzx.symm.trans hzu) i
      simp only [Pi.add_apply] at hi
      omega
    exact hn hx (heq ▸ hu)
  · exact double_ne_edgeMidpoint x (q.adj_of_mem_edges huv) (hzx.symm.trans hzu)
  · exact double_ne_edgeMidpoint u (p.adj_of_mem_edges hxy) (hzu.symm.trans hzx)
  · have he := (edgeMidpoint_eq_iff (p.adj_of_mem_edges hxy) (q.adj_of_mem_edges huv)).mp
      (hzx.symm.trans hzu)
    have hx := p.fst_mem_support_of_mem_edges hxy
    have hxq := q.fst_mem_support_of_mem_edges (he.symm ▸ huv)
    exact hn hx hxq

end

end Percolation.Literature
