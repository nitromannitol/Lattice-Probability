import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Prod

/-! Subdividing one side of a dependent product of sets. -/

open Set

namespace LatticeProb

/-- Replacing one side of a box by a union gives the union of the boxes
obtained by replacing that side by each member of the family. -/
theorem pi_update_iUnion {ι κ : Type*} [DecidableEq ι] {α : ι → Type*} (i : ι)
    (A : ∀ j, Set (α j)) (C : κ → Set (α i)) :
    univ.pi (Function.update A i (⋃ k, C k)) =
      ⋃ k, univ.pi (Function.update A i (C k)) := by
  classical
  ext x
  simp only [mem_iUnion]
  constructor
  · intro hx
    have hi : x i ∈ ⋃ k, C k := by
      simpa only [Function.update_self] using hx i (mem_univ i)
    obtain ⟨k, hk⟩ := mem_iUnion.mp hi
    refine ⟨k, ?_⟩
    intro j _
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using hk
    · simpa only [Function.update_of_ne h] using hx j (mem_univ j)
  · rintro ⟨k, hx⟩ j _
    by_cases h : j = i
    · subst j
      simpa only [Function.update_self] using
        (mem_iUnion.mpr ⟨k, by simpa only [Function.update_self] using hx i (mem_univ i)⟩)
    · simpa only [Function.update_of_ne h] using hx j (mem_univ j)

/-- Disjoint subdivisions of one side yield disjoint product boxes. -/
theorem pairwiseDisjoint_pi_update {ι κ : Type*} [DecidableEq ι] {α : ι → Type*} (i : ι)
    (A : ∀ j, Set (α j)) (C : κ → Set (α i))
    (hC : Pairwise fun k l => Disjoint (C k) (C l)) :
    Pairwise fun k l => Disjoint (univ.pi (Function.update A i (C k)))
      (univ.pi (Function.update A i (C l))) := by
  classical
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' : x i ∈ C k := by simpa only [Function.update_self] using hx i (mem_univ i)
  have hy' : x i ∈ C l := by simpa only [Function.update_self] using hy i (mem_univ i)
  exact Set.disjoint_left.mp (hC hkl) hx' hy'

end LatticeProb
