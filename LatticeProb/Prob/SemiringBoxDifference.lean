import LatticeProb.Prob.RefinedBoxDifference
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Data.Fintype.Sigma

/-! Finite disjoint partitions of differences of dependent boxes. -/

open Set MeasureTheory

namespace LatticeProb

/-- A difference of finite dependent boxes with semiring sides is a finite
union of pairwise disjoint boxes with sides in the corresponding semirings. -/
theorem pi_sdiff_pi_finite_disjoint {n : ℕ} {α : Fin n → Type*}
    (C : ∀ i, Set (Set (α i))) (hC : ∀ i, IsSetSemiring (C i))
    (A B : ∀ i, Set (α i)) (hA : ∀ i, A i ∈ C i) (hB : ∀ i, B i ∈ C i) :
    ∃ F : Finset (Set (∀ i, α i)),
      (∀ s ∈ F, ∃ D : ∀ i, Set (α i), (∀ i, D i ∈ C i) ∧ s = univ.pi D) ∧
      PairwiseDisjoint (F : Set (Set (∀ i, α i))) id ∧
      univ.pi A \ univ.pi B = ⋃₀ (F : Set (Set (∀ i, α i))) := by
  classical
  let P (i : Fin n) := (hC i).disjointOfDiff (hA i) (hB i)
  let κ (i : Fin n) := {s : Set (α i) // s ∈ P i}
  let D : ∀ i, κ i → Set (α i) := fun _ s => s.1
  have hD (i : Fin n) : A i \ B i = ⋃ k, D i k := by
    rw [← (hC i).sUnion_disjointOfDiff (hA i) (hB i)]
    ext x
    simp only [mem_sUnion, Finset.mem_coe, mem_iUnion, D, κ, P]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨⟨s, hs⟩, hx⟩
    · rintro ⟨⟨s, hs⟩, hx⟩
      exact ⟨s, hs, hx⟩
  have hdisj (i : Fin n) : Pairwise fun k l : κ i => Disjoint (D i k) (D i l) := by
    intro k l hkl
    apply (hC i).pairwiseDisjoint_disjointOfDiff (hA i) (hB i) k.2 l.2
    intro h
    exact hkl (Subtype.ext h)
  let box : (Σ i, κ i) → Set (∀ i, α i) :=
    fun p => refinedFirstFailureBox A B p.1 (D p.1 p.2)
  let F : Finset (Set (∀ i, α i)) := Finset.univ.image box
  refine ⟨F, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨⟨i, k⟩, _, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨Function.update
      (fun j => if j < i then A j ∩ B j else if j = i then A j \ B j else A j)
      i (D i k), ?_, rfl⟩
    intro j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
      exact (hC i).subset_disjointOfDiff (hA i) (hB i) k.2
    · rw [Function.update_of_ne h]
      by_cases hji : j < i
      · simp only [hji, ↓reduceIte]
        exact (hC j).inter_mem _ (hA j) _ (hB j)
      · simp only [hji, h, ↓reduceIte]
        exact hA j
  · intro s hs t ht hst
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ht
    exact pairwiseDisjoint_refinedFirstFailureBox A B D hD hdisj (by
      intro hpq
      subst q
      exact hst rfl)
  · rw [pi_sdiff_pi_eq_iUnion_refinedFirstFailureBox A B D hD]
    ext x
    simp only [mem_iUnion, mem_sUnion, Finset.mem_coe, F, Finset.mem_image,
      Finset.mem_univ, true_and, box, exists_exists_eq_and]
    constructor
    · rintro ⟨i, k, hx⟩
      exact ⟨⟨i, k⟩, hx⟩
    · rintro ⟨⟨i, k⟩, hx⟩
      exact ⟨i, k, hx⟩

end LatticeProb
