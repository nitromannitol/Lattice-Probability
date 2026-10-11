/-
# Boundary cases for orthonormal frames

Degree zero is the empty wedge. Overfull degree is identically zero. Frame
normalization supplies the unit and orthogonality facts used by recovery and
increasing-event comparison.
-/

import LatticeProb.LinearAlgebra.DeterminantEvent



namespace LatticeProb.SubsetContraction
open scoped BigOperators Classical Matrix
noncomputable section

/-- Degree-zero coefficients are one at the empty subset and zero elsewhere. -/
theorem determinantCoeff_degree_zero {n : ℕ} (V : Matrix (Fin n) (Fin 0) ℝ)
    (S : Finset (Fin n)) : determinantCoeff V S = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · subst S
    rw [if_pos rfl, determinantCoeff_of_card_eq V ∅ (Finset.card_empty), Matrix.det_isEmpty]
  · rw [if_neg hS]
    exact determinantCoeff_of_card_ne V S (fun h => hS (Finset.card_eq_zero.mp h))

/-- Coefficients above the number of coordinates vanish on every subset. -/
theorem determinantCoeff_eq_zero_of_lt_degree {n k : ℕ}
    (V : Matrix (Fin n) (Fin k) ℝ) (hnk : n < k) : determinantCoeff V = 0 := by
  funext S
  apply determinantCoeff_of_card_ne
  have hcard := S.card_le_univ
  rw [Fintype.card_fin] at hcard
  omega

/-- A full-degree frame has its full determinant at the full subset, and zero
at every proper subset. -/
theorem determinantCoeff_full_degree {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    determinantCoeff V S = if S = Finset.univ then V.det else 0 := by
  by_cases hS : S = Finset.univ
  · subst S
    have hcard : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
    have he : ((Finset.univ : Finset (Fin n)).orderEmbOfFin hcard : Fin n → Fin n) = id := by
      symm
      apply Finset.orderEmbOfFin_unique hcard
      · intro i; exact Finset.mem_univ i
      · exact strictMono_id
    rw [if_pos rfl, determinantCoeff_of_card_eq V _ hcard, he, Matrix.submatrix_id_id]
  · rw [if_neg hS]
    apply determinantCoeff_of_card_ne
    intro hcard
    exact hS (Finset.eq_univ_of_card S (hcard.trans (Fintype.card_fin n).symm))

/-- Adding a column to a full-degree frame has identically zero coefficients. -/
theorem determinantCoeff_prependColumn_full_degree {n : ℕ} (u : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    determinantCoeff (prependColumn u V) = 0 :=
  determinantCoeff_eq_zero_of_lt_degree _ (Nat.lt_succ_self n)

/-- For an orthonormal first-column extension, its first column has unit
squared length and is perpendicular to every remaining column. -/
theorem unit_orthogonal_of_prependColumn_orthonormal {n k : ℕ} (u : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hUV : (prependColumn u V).transpose * prependColumn u V = 1) :
    (∑ i, u i ^ 2 = 1) ∧ (∀ j, ∑ i, u i * V i j = 0) := by
  constructor
  · have h := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ => M 0 0) hUV
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, prependColumn, Fin.cons_zero,
      Matrix.one_apply, ↓reduceIte, pow_two] using h
  · intro j
    have h := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ => M 0 j.succ) hUV
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, prependColumn, Fin.cons_zero,
      Fin.cons_succ, Matrix.one_apply, (Fin.succ_ne_zero j).symm, ↓reduceIte] using h

/-- **Exterior recovery at the endpoint degrees.** An orthonormal extended frame produces exact recovery and the increasing
finset event inequality; all recovery prerequisites are derived internally. -/
theorem recovery_event_of_prependColumn_orthonormal {n k : ℕ} (u : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hUV : (prependColumn u V).transpose * prependColumn u V = 1)
    (A : Set (Finset (Fin n))) (hA : ∀ S ∈ A, ∀ i, insert i S ∈ A) :
    finsetContract u (determinantCoeff (prependColumn u V)) = determinantCoeff V ∧
    (∑ S : Finset (Fin n), A.indicator (fun S => determinantCoeff V S ^ 2) S) ≤
      ∑ S : Finset (Fin n),
        A.indicator (fun S => determinantCoeff (prependColumn u V) S ^ 2) S := by
  obtain ⟨hunit, horth⟩ := unit_orthogonal_of_prependColumn_orthonormal u V hUV
  exact ⟨finsetContract_prependColumn u V hunit horth,
    sum_indicator_determinantCoeff_sq_le_prependColumn u V hunit horth A hA⟩

end
end LatticeProb.SubsetContraction
