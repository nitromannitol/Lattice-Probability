import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic

/-! Disjoint decompositions of differences of finite-coordinate boxes. -/

open Set

namespace LatticeProb

/-- The part of a box where the first side of another box that fails is `i`. -/
def firstFailureBox {n : ℕ} {α : Fin n → Type*}
    (A B : ∀ i, Set (α i)) (i : Fin n) : Set (∀ i, α i) :=
  univ.pi fun j => if j < i then A j ∩ B j else if j = i then A j \ B j else A j

/-- The difference of two finite boxes is the union of the first-failure boxes. -/
theorem pi_sdiff_pi_eq_iUnion_firstFailureBox {n : ℕ} {α : Fin n → Type*}
    (A B : ∀ i, Set (α i)) :
    univ.pi A \ univ.pi B = ⋃ i, firstFailureBox A B i := by
  classical
  ext x
  simp only [mem_sdiff, mem_pi, mem_univ, true_implies, mem_iUnion]
  constructor
  · rintro ⟨hA, hB⟩
    have hfail : ∃ k : ℕ, ∃ hk : k < n, x ⟨k, hk⟩ ∉ B ⟨k, hk⟩ := by
      obtain ⟨i, hi⟩ := not_forall.mp hB
      exact ⟨i.val, i.isLt, hi⟩
    let k := Nat.find hfail
    obtain ⟨hk, hnot⟩ := Nat.find_spec hfail
    let i : Fin n := ⟨k, hk⟩
    refine ⟨i, ?_⟩
    intro j _
    change x j ∈ if j < i then A j ∩ B j else if j = i then A j \ B j else A j
    split_ifs with hji heq
    · refine ⟨hA j, ?_⟩
      by_contra hj
      exact Nat.find_min hfail hji ⟨j.isLt, hj⟩
    · subst j
      exact ⟨hA i, hnot⟩
    · exact hA j
  · rintro ⟨i, hi⟩
    have hside : ∀ j, x j ∈ if j < i then A j ∩ B j else if j = i then A j \ B j else A j := by
      simpa only [firstFailureBox, mem_pi, mem_univ, true_implies] using hi
    constructor
    · intro j
      have hj := hside j
      split_ifs at hj
      · exact hj.1
      · exact hj.1
      · exact hj
    · intro hB
      have hj : x i ∈ A i \ B i := by simpa using hside i
      exact hj.2 (hB i)

/-- First-failure boxes at distinct coordinates are disjoint. -/
theorem pairwiseDisjoint_firstFailureBox {n : ℕ} {α : Fin n → Type*}
    (A B : ∀ i, Set (α i)) : Pairwise (fun i j => Disjoint (firstFailureBox A B i) (firstFailureBox A B j)) := by
  classical
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hi := hx i (mem_univ i)
  have hj := hy j (mem_univ j)
  change x i ∈ if i < i then A i ∩ B i else if i = i then A i \ B i else A i at hi
  change x j ∈ if j < j then A j ∩ B j else if j = j then A j \ B j else A j at hj
  have hi' : x i ∈ A i \ B i := by simpa using hi
  have hj' : x j ∈ A j \ B j := by simpa using hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := hy i (mem_univ i)
    change x i ∈ if i < j then A i ∩ B i else if i = j then A i \ B i else A i at h
    simp only [hlt, ↓reduceIte] at h
    exact hi'.2 h.2
  · have h := hx j (mem_univ j)
    change x j ∈ if j < i then A j ∩ B j else if j = i then A j \ B j else A j at h
    simp only [hgt, ↓reduceIte] at h
    exact hj'.2 h.2

end LatticeProb
