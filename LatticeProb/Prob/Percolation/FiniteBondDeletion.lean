import LatticeProb.Prob.Percolation.LatticeBondFiniteFlip
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Finite flips as actual edge deletion

Finite flips toggle genuine unordered bonds. When every selected bond is open, the resulting
open graph is exactly the original graph with the ambient unordered endpoints removed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

variable {d : ℕ}

/-- The ambient unordered edges of a finite set of genuine lattice bonds. -/
def deletedBondEdges (F : Finset (Bond d)) : Set (Sym2 (Vertex d)) :=
  Subtype.val '' (F : Set (Bond d))

/-- Membership at every genuine bond is exactly membership in the original finite set. -/
theorem val_mem_deletedBondEdges (F : Finset (Bond d)) (e : Bond d) :
    e.val ∈ deletedBondEdges F ↔ e ∈ F := by
  constructor
  · rintro ⟨a, ha, he⟩
    exact (Subtype.ext he : a = e) ▸ ha
  · intro he
    exact ⟨e, he, rfl⟩

/-- The complete pointwise adjacency formula includes both opening and closing selected bonds. -/
theorem openGraph_finiteBondFlip_adj_iff (F : Finset (Bond d)) (ω : Configuration d)
    (x y : Vertex d) :
    (openGraph (finiteBondFlip F ω)).Adj x y ↔
      ∃ h : (nearestNeighborGraph d).Adj x y,
        (bondOfAdjacent h ∈ F ∧ ω (bondOfAdjacent h) = false) ∨
        (bondOfAdjacent h ∉ F ∧ ω (bondOfAdjacent h) = true) := by
  classical
  simp only [openGraph_adj_iff, finiteBondFlip, BernoulliFiniteFlip.flip]
  apply exists_congr
  intro h
  by_cases he : bondOfAdjacent h ∈ F <;> cases ω (bondOfAdjacent h) <;>
    simp only [he, if_true, if_false, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_eq_false, and_true, and_false, or_false, false_or,
      not_true_eq_false, not_false_eq_true]

/-- Flipping an all-open finite bond set deletes exactly its actual ambient unordered edges. -/
theorem openGraph_finiteBondFlip_eq_deleteEdges_of_all_open (F : Finset (Bond d))
    (ω : Configuration d) (hopen : ∀ e ∈ F, ω e = true) :
    openGraph (finiteBondFlip F ω) = (openGraph ω).deleteEdges (deletedBondEdges F) := by
  classical
  ext x y
  rw [openGraph_finiteBondFlip_adj_iff, SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨h, ⟨he, hc⟩ | ⟨he, ho⟩⟩
    · have := hopen _ he
      rw [hc] at this
      exact (Bool.false_ne_true this).elim
    · exact ⟨⟨h, ho⟩, (val_mem_deletedBondEdges F (bondOfAdjacent h)).not.mpr he⟩
  · rintro ⟨⟨h, ho⟩, he⟩
    exact ⟨h, Or.inr ⟨(val_mem_deletedBondEdges F (bondOfAdjacent h)).not.mp he, ho⟩⟩

/-- All-open finite flips can only remove open adjacencies. -/
theorem openGraph_finiteBondFlip_le_of_all_open (F : Finset (Bond d))
    (ω : Configuration d) (hopen : ∀ e ∈ F, ω e = true) :
    openGraph (finiteBondFlip F ω) ≤ openGraph ω := by
  rw [openGraph_finiteBondFlip_eq_deleteEdges_of_all_open F ω hopen]
  exact SimpleGraph.deleteEdges_le _

end LatticeProb.Percolation
