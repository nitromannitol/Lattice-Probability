module

/-
# Increasing events and orthogonal determinant extensions

Upward closure produces the contraction localization identity. The sharp CAR
contraction bound then compares the squared determinant weights of the two
frames, without any intermediate probability laws.
-/

public import LatticeProb.LinearAlgebra.DeterminantAnnihilation

@[expose] public section



namespace LatticeProb.SubsetContraction
open scoped BigOperators Classical
noncomputable section

/-- On an insertion-closed event, contraction only reads coefficients within
that event: `P_A C_u = P_A C_u P_A`. -/
theorem indicator_finsetContract {n : ℕ} (u : Fin n → ℝ)
    (x : Finset (Fin n) → ℝ) (A : Set (Finset (Fin n)))
    (hA : ∀ S ∈ A, ∀ i, insert i S ∈ A) :
    A.indicator (finsetContract u x) =
      A.indicator (finsetContract u (A.indicator x)) := by
  funext S
  by_cases hS : S ∈ A
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS]
    apply Finset.sum_congr rfl
    intro i _
    rw [Set.indicator_of_mem (hA S hS i)]
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS]

/-- **Rank-one increasing-event inequality.** A unit vector orthogonal to all
frame columns increases the squared determinant weight of every increasing
event when prepended as the first column. -/
theorem sum_sq_indicator_determinantCoeff_le_prependColumn {n k : ℕ}
    (u : Fin n → ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (hunit : ∑ i, u i ^ 2 = 1) (horth : ∀ j, ∑ i, u i * V i j = 0)
    (A : Set (Finset (Fin n))) (hA : ∀ S ∈ A, ∀ i, insert i S ∈ A) :
    (∑ S : Finset (Fin n), (A.indicator (determinantCoeff V) S) ^ 2) ≤
      ∑ S : Finset (Fin n), (A.indicator (determinantCoeff (prependColumn u V)) S) ^ 2 := by
  have h := sum_sq_finset_contraction_le n u
    (A.indicator (determinantCoeff (prependColumn u V)))
  change (∑ S : Finset (Fin n),
    finsetContract u (A.indicator (determinantCoeff (prependColumn u V))) S ^ 2) ≤ _ at h
  rw [hunit, one_mul] at h
  calc
    _ = ∑ S : Finset (Fin n),
        (A.indicator (finsetContract u
          (A.indicator (determinantCoeff (prependColumn u V)))) S) ^ 2 := by
      rw [← indicator_finsetContract u _ A hA, finsetContract_prependColumn u V hunit horth]
    _ ≤ ∑ S : Finset (Fin n),
        finsetContract u (A.indicator (determinantCoeff (prependColumn u V))) S ^ 2 := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : S ∈ A
      · rw [Set.indicator_of_mem hS]
      · rw [Set.indicator_of_notMem hS, zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg _
    _ ≤ _ := h

/-- The same comparison written in the original finset event-sum form for
actual squared ordered-minor weights. -/
theorem sum_indicator_determinantCoeff_sq_le_prependColumn {n k : ℕ}
    (u : Fin n → ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (hunit : ∑ i, u i ^ 2 = 1) (horth : ∀ j, ∑ i, u i * V i j = 0)
    (A : Set (Finset (Fin n))) (hA : ∀ S ∈ A, ∀ i, insert i S ∈ A) :
    (∑ S : Finset (Fin n), A.indicator (fun S => determinantCoeff V S ^ 2) S) ≤
      ∑ S : Finset (Fin n),
        A.indicator (fun S => determinantCoeff (prependColumn u V) S ^ 2) S := by
  have hpow (x : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
      A.indicator (fun S => x S ^ 2) S = (A.indicator x S) ^ 2 := by
    by_cases hS : S ∈ A
    · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS]
    · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS,
        zero_pow (by decide : 2 ≠ 0)]
  simp only [hpow]
  exact sum_sq_indicator_determinantCoeff_le_prependColumn u V hunit horth A hA

end
end LatticeProb.SubsetContraction
