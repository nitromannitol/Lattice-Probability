import LatticeProb.Vendor.FormalMathPercolation.Literature.PlanarDuality

/-!
# Subdivision of lattice walks

A nearest-neighbor walk on the square lattice can be embedded in the doubled lattice by
replacing each edge with two edges through its midpoint. Its support and coordinate bounds
are described in terms of the original walk.
-/

namespace Percolation.Literature

open SimpleGraph

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

private theorem adj_double_add {x y : V} (h : G.Adj x y) : G.Adj (x + x) (x + y) := by
  apply adj_of_stepKind
  rcases stepKind_of_adj h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
  · apply StepKind.right <;> simp only [Pi.add_apply] <;> omega
  · apply StepKind.left <;> simp only [Pi.add_apply] <;> omega
  · apply StepKind.up <;> simp only [Pi.add_apply] <;> omega
  · apply StepKind.down <;> simp only [Pi.add_apply] <;> omega

private theorem adj_add_double {x y : V} (h : G.Adj x y) : G.Adj (x + y) (y + y) := by
  simpa only [add_comm] using (adj_double_add h.symm).symm

/-- Replace each lattice edge by two edges through the sum of its endpoints. -/
def subdivideWalk {a b : V} : G.Walk a b → G.Walk (a + a) (b + b)
  | .nil => .nil
  | .cons h p => .cons (adj_double_add h) (.cons (adj_add_double h) (subdivideWalk p))

/-- The subdivided walk contains exactly the doubled vertices and the edge midpoints. -/
theorem mem_support_subdivideWalk {a b z : V} (p : G.Walk a b) :
    z ∈ (subdivideWalk p).support ↔
      (∃ x ∈ p.support, z = x + x) ∨
        ∃ x y, s(x, y) ∈ p.edges ∧ z = x + y := by
  induction p with
  | nil => simp [subdivideWalk]
  | @cons x y b h p ih =>
    simp only [subdivideWalk, Walk.support_cons, Walk.edges_cons, List.mem_cons, ih]
    constructor
    · rintro (hz | hz | ⟨v, hv, hz⟩ | ⟨v, w, he, hz⟩)
      · exact Or.inl ⟨x, Or.inl rfl, hz⟩
      · exact Or.inr ⟨x, y, Or.inl rfl, hz⟩
      · exact Or.inl ⟨v, Or.inr hv, hz⟩
      · exact Or.inr ⟨v, w, Or.inr he, hz⟩
    · rintro (⟨v, hv | hv, hz⟩ | ⟨v, w, he | he, hz⟩)
      · subst v; exact Or.inl hz
      · exact Or.inr (Or.inr (Or.inl ⟨v, hv, hz⟩))
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inl (by simpa only [add_comm] using hz))
      · exact Or.inr (Or.inr (Or.inr ⟨v, w, he, hz⟩))

/-- Coordinate bounds on a walk double under subdivision. -/
theorem subdivideWalk_coordinate_bounds {a b : V} (p : G.Walk a b) (i : Fin 2)
    (L R : ℤ) (h : ∀ x ∈ p.support, L ≤ x i ∧ x i ≤ R) :
    ∀ z ∈ (subdivideWalk p).support, 2 * L ≤ z i ∧ z i ≤ 2 * R := by
  intro z hz
  rcases (mem_support_subdivideWalk p).mp hz with ⟨x, hx, rfl⟩ | ⟨x, y, he, rfl⟩
  · have hx' := h x hx
    simp only [Pi.add_apply]
    omega
  · have hx := h x (p.fst_mem_support_of_mem_edges he)
    have hy := h y (p.snd_mem_support_of_mem_edges he)
    simp only [Pi.add_apply]
    omega

end

end Percolation.Literature
