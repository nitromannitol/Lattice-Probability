module

/-
# Endpoint comparison after deleting orthogonal columns

Repeated rank-one contraction compares only the squared determinant weights of
the endpoint frames. No intermediate probability distributions are constructed.
-/

public import LatticeProb.LinearAlgebra.DeterminantBoundaries

@[expose] public section



namespace LatticeProb.SubsetContraction
open scoped BigOperators Classical Matrix
noncomputable section

/-- Delete the first column of a frame. -/
def dropFirstColumn {n k : ℕ} (U : Matrix (Fin n) (Fin (k + 1)) ℝ) :
    Matrix (Fin n) (Fin k) ℝ := U.submatrix id Fin.succ

/-- Deleting the first column preserves orthonormality of the remaining columns. -/
theorem dropFirstColumn_orthonormal {n k : ℕ}
    (U : Matrix (Fin n) (Fin (k + 1)) ℝ) (hU : U.transpose * U = 1) :
    (dropFirstColumn U).transpose * dropFirstColumn U = 1 := by
  have h : (U.transpose * U).submatrix Fin.succ Fin.succ = 1 := by
    rw [hU, Matrix.submatrix_one _ (Fin.succ_injective k)]
  rw [← Matrix.submatrix_mul_equiv U.transpose U Fin.succ (Equiv.refl (Fin n)) Fin.succ] at h
  exact h

/-- The frame is exactly its first column prepended to the remaining columns. -/
theorem prependColumn_dropFirstColumn {n k : ℕ}
    (U : Matrix (Fin n) (Fin (k + 1)) ℝ) :
    prependColumn (fun i => U i 0) (dropFirstColumn U) = U := by
  funext i
  exact Fin.cons_self_tail (U i)

/-- Deleting one orthonormal column decreases every increasing-event squared
coefficient sum. The required orthogonal recovery is produced internally. -/
theorem sum_indicator_determinantCoeff_sq_dropFirstColumn_le {n k : ℕ}
    (U : Matrix (Fin n) (Fin (k + 1)) ℝ) (hU : U.transpose * U = 1)
    (A : Set (Finset (Fin n))) (hA : ∀ S ∈ A, ∀ i, insert i S ∈ A) :
    (∑ S : Finset (Fin n), A.indicator (fun S => determinantCoeff (dropFirstColumn U) S ^ 2) S) ≤
      ∑ S : Finset (Fin n), A.indicator (fun S => determinantCoeff U S ^ 2) S := by
  have hframe : (prependColumn (fun i => U i 0) (dropFirstColumn U)).transpose *
      prependColumn (fun i => U i 0) (dropFirstColumn U) = 1 := by
    rw [prependColumn_dropFirstColumn U]
    exact hU
  have h := (recovery_event_of_prependColumn_orthonormal (fun i => U i 0)
    (dropFirstColumn U) hframe A hA).2
  rwa [prependColumn_dropFirstColumn U] at h

/-- Delete `m` leading columns while retaining the exact order of the last `k`. -/
def dropLeadingColumns {n k m : ℕ} (U : Matrix (Fin n) (Fin (k + m)) ℝ) :
    Matrix (Fin n) (Fin k) ℝ :=
  U.submatrix id (fun j => ⟨m + j.val, by omega⟩)

/-- **Endpoint event comparison.** Deleting any number of leading orthonormal
columns decreases the increasing-event squared determinant weight. Only the
endpoint coefficients occur in the statement. -/
theorem sum_indicator_determinantCoeff_sq_dropLeadingColumns_le {n k m : ℕ}
    (U : Matrix (Fin n) (Fin (k + m)) ℝ) (hU : U.transpose * U = 1)
    (A : Set (Finset (Fin n))) (hA : ∀ S ∈ A, ∀ i, insert i S ∈ A) :
    (∑ S : Finset (Fin n), A.indicator (fun S => determinantCoeff (dropLeadingColumns U) S ^ 2) S) ≤
      ∑ S : Finset (Fin n), A.indicator (fun S => determinantCoeff U S ^ 2) S := by
  induction m with
  | zero =>
    have he : dropLeadingColumns U = U := by
      ext i j
      change U i ⟨0 + j.val, by omega⟩ = U i j
      congr 1
      apply Fin.ext
      exact Nat.zero_add j.val
    rw [he]
  | succ m ih =>
    have he : dropLeadingColumns (k := k) (m := m) (dropFirstColumn U) =
        dropLeadingColumns (k := k) (m := m + 1) U := by
      ext i j
      have hj : j.val < k := j.isLt
      have hI : m + j.val < k + m := by omega
      change U i (Fin.succ (⟨m + j.val, hI⟩ : Fin (k + m))) =
        U i ⟨(m + 1) + j.val, by omega⟩
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    calc
      _ = ∑ S : Finset (Fin n),
          A.indicator (fun S => determinantCoeff (dropLeadingColumns (dropFirstColumn U)) S ^ 2) S := by
        rw [he]
      _ ≤ ∑ S : Finset (Fin n),
          A.indicator (fun S => determinantCoeff (dropFirstColumn U) S ^ 2) S :=
        ih (dropFirstColumn U) (dropFirstColumn_orthonormal U hU)
      _ ≤ _ := sum_indicator_determinantCoeff_sq_dropFirstColumn_le U hU A hA

end
end LatticeProb.SubsetContraction
