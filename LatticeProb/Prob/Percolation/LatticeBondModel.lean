import LatticeProb.Graph.Zd

/-!
# Bonds of the integer lattice

The vertices are integer coordinate vectors and bonds are unordered pairs at ℓ¹ distance one.
The existing unit-vector lattice graph is characterized by precisely this distance condition.
Configurations assign a Boolean to each genuine bond, in arbitrary dimension, including zero.
-/

namespace LatticeProb.Percolation

open scoped BigOperators

variable {d : ℕ}

/-- Integer-coordinate vertices of the lattice. -/
abbrev Vertex (d : ℕ) := Fin d → ℤ

/-- The ℓ¹ distance, using integer absolute values, rather than a Euclidean or sup distance. -/
def latticeL1Dist (x y : Vertex d) : ℤ := ∑ i, |x i - y i|

/-- Unordered nearest-neighbor bonds, with the literal ℓ¹-distance-one carrier. -/
abbrev Bond (d : ℕ) :=
  {e : Sym2 (Vertex d) // ∃ x y : Vertex d,
    e = s(x, y) ∧ (∑ i, |x i - y i|) = 1}

/-- A deterministic assignment of open or closed status to every genuine lattice bond. -/
abbrev Configuration (d : ℕ) := Bond d → Bool

/-- The nearest-neighbor graph already supplied by the lattice library. -/
abbrev nearestNeighborGraph (d : ℕ) := lattice d

/-- The unit-vector lattice adjacency is exactly ℓ¹ distance one. -/
theorem lattice_adj_iff_l1Dist {x y : Vertex d} :
    (nearestNeighborGraph d).Adj x y ↔ latticeL1Dist x y = 1 := by
  constructor
  · rintro ⟨i, rfl | rfl⟩ <;>
      simp [latticeL1Dist, unit, Pi.single_apply, apply_ite abs]
  · intro hsum
    have hex : ∃ i, x i - y i ≠ 0 := by
      by_contra! h
      have hz : latticeL1Dist x y = 0 := by simp [latticeL1Dist, h]
      omega
    obtain ⟨i, hi⟩ := hex
    have hle : |x i - y i| ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (x j - y j)) (Finset.mem_univ i)
    have hone : |x i - y i| = 1 := by
      have := abs_pos.mpr hi
      omega
    have herase : ∑ j ∈ Finset.univ.erase i, |x j - y j| = 0 := by
      have he := Finset.sum_erase_add Finset.univ (fun j => |x j - y j|)
        (Finset.mem_univ i)
      change (∑ j, |x j - y j|) = 1 at hsum
      omega
    have hother : ∀ j, j ≠ i → x j = y j := by
      intro j hj
      have hjle := Finset.single_le_sum (fun k _ => abs_nonneg (x k - y k))
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      rw [herase] at hjle
      have hz := abs_nonneg (x j - y j)
      have heq : |x j - y j| = 0 := le_antisymm hjle hz
      exact sub_eq_zero.mp (abs_eq_zero.mp heq)
    have hor : x i - y i = 1 ∨ x i - y i = -1 := (abs_eq (by norm_num)).mp hone
    refine ⟨i, ?_⟩
    rcases hor with hp | hm
    · right
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Pi.add_apply, unit, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hj]
        exact (hother j hj).trans (add_zero _).symm
    · left
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Pi.add_apply, unit, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hj]
        exact (hother j hj).symm.trans (add_zero _).symm

/-- The bond determined by adjacent vertices; no endpoint ordering is chosen. -/
def bondOfAdjacent {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) : Bond d :=
  ⟨s(x, y), x, y, rfl, lattice_adj_iff_l1Dist.mp h⟩

/-- Reversing the endpoint presentation does not change its bond. -/
theorem bondOfAdjacent_symm {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent h.symm = bondOfAdjacent h := by
  apply Subtype.ext
  exact Sym2.eq_swap

end LatticeProb.Percolation
