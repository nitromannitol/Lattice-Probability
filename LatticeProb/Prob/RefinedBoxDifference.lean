import LatticeProb.Prob.FiniteBoxDifference
import LatticeProb.Prob.BoxSideUnion

/-! Refinements of the first-failure partition of finite box differences. -/

open Set

namespace LatticeProb

/-- A first-failure box with its failing side replaced by a chosen set. -/
def refinedFirstFailureBox {n : ℕ} {α : Fin n → Type*}
    (A B : ∀ i, Set (α i)) (i : Fin n) (C : Set (α i)) : Set (∀ i, α i) :=
  univ.pi (Function.update
    (fun j => if j < i then A j ∩ B j else if j = i then A j \ B j else A j) i C)

/-- Refining the failing sides gives a union decomposition of the box difference. -/
theorem pi_sdiff_pi_eq_iUnion_refinedFirstFailureBox {n : ℕ} {α : Fin n → Type*}
    {κ : Fin n → Type*} (A B : ∀ i, Set (α i)) (C : ∀ i, κ i → Set (α i))
    (hC : ∀ i, A i \ B i = ⋃ k, C i k) :
    univ.pi A \ univ.pi B = ⋃ i, ⋃ k, refinedFirstFailureBox A B i (C i k) := by
  classical
  rw [pi_sdiff_pi_eq_iUnion_firstFailureBox]
  congr 1
  funext i
  have hs : (fun j => if j < i then A j ∩ B j else if j = i then A j \ B j else A j) =
      Function.update (fun j => if j < i then A j ∩ B j else if j = i then A j \ B j else A j)
        i (⋃ k, C i k) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [lt_self_iff_false, ↓reduceIte, Function.update_self]
      exact hC i
    · simp only [Function.update_of_ne h]
  unfold firstFailureBox
  rw [hs, pi_update_iUnion]
  rfl

/-- Disjoint side refinements produce a pairwise disjoint family of boxes. -/
theorem pairwiseDisjoint_refinedFirstFailureBox {n : ℕ} {α : Fin n → Type*}
    {κ : Fin n → Type*} (A B : ∀ i, Set (α i)) (C : ∀ i, κ i → Set (α i))
    (hC : ∀ i, A i \ B i = ⋃ k, C i k)
    (hdisj : ∀ i, Pairwise fun k l => Disjoint (C i k) (C i l)) :
    Pairwise fun p q : (Σ i, κ i) =>
      Disjoint (refinedFirstFailureBox A B p.1 (C p.1 p.2))
        (refinedFirstFailureBox A B q.1 (C q.1 q.2)) := by
  classical
  have hsub (i : Fin n) (k : κ i) :
      refinedFirstFailureBox A B i (C i k) ⊆ firstFailureBox A B i := by
    intro x hx j hj
    have hxj := hx j hj
    by_cases h : j = i
    · subst j
      have hx' : x i ∈ C i k := by
        simpa only [refinedFirstFailureBox, Function.update_self] using hxj
      have hx'' : x i ∈ A i \ B i := by
        rw [hC i]
        exact mem_iUnion.mpr ⟨k, hx'⟩
      simpa only [firstFailureBox, lt_self_iff_false, ↓reduceIte] using hx''
    · simpa only [refinedFirstFailureBox, firstFailureBox, Function.update_of_ne h] using hxj
  rintro ⟨i, k⟩ ⟨j, l⟩ hne
  by_cases h : i = j
  · subst j
    have hkl : k ≠ l := by
      intro h
      subst l
      exact hne rfl
    exact pairwiseDisjoint_pi_update i
      (fun j => if j < i then A j ∩ B j else if j = i then A j \ B j else A j)
      (C i) (hdisj i) hkl
  · exact (pairwiseDisjoint_firstFailureBox A B h).mono (hsub i k) (hsub j l)

end LatticeProb
