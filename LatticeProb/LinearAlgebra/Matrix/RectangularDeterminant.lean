/-
# Determinants of rectangular matrix products

Expand the determinant of a square product through choices of rows of its right
factor. Choices that repeat a row contribute zero, including when the shared
index carrier is smaller than the square index carrier.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic



namespace Matrix
open scoped BigOperators Classical
variable {m e R : Type*} [Fintype m] [DecidableEq m] [CommRing R]

/-- Expand a rectangular product's determinant by choosing one row of the right
factor for each row of the square product. Empty index carriers are included. -/
theorem det_mul_eq_sum_pi [Fintype e] (A : Matrix m e R) (B : Matrix e m R) :
    (A * B).det =
      ∑ f : m → e, (∏ i : m, A i (f i)) * (B.submatrix f id).det := by
  classical
  calc
    (A * B).det = det (fun i => ∑ a : e, A i a • B a) := by
      congr 1
      ext i j
      simp only [mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ f : m → e, det (fun i => A i (f i) • B (f i)) :=
      (detRowAlternating (R := R) (n := m)).toMultilinearMap.map_sum
        (fun i a => A i a • B a)
    _ = ∑ f : m → e, (∏ i : m, A i (f i)) * (B.submatrix f id).det := by
      apply Finset.sum_congr rfl
      intro f _
      exact det_mul_column (fun i => A i (f i)) (B.submatrix f id)

/-- Repeating a row in a square submatrix makes its determinant zero. The ambient
row carrier need not be finite. -/
theorem det_submatrix_eq_zero_of_not_injective (B : Matrix e m R) (f : m → e)
    (hf : ¬Function.Injective f) : (B.submatrix f id).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  apply det_zero_of_row_eq hne
  exact congrArg B hij

/-- **Rectangular determinant expansion.** Only injective row choices contribute to the determinant of a rectangular
product; no cardinality comparison or nonemptiness hypothesis is required. -/
theorem det_mul_eq_sum_injective [Fintype e] (A : Matrix m e R) (B : Matrix e m R) :
    (A * B).det =
      ∑ f : m → e with Function.Injective f,
        (∏ i : m, A i (f i)) * (B.submatrix f id).det := by
  classical
  rw [det_mul_eq_sum_pi]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro f _ hf
  rw [det_submatrix_eq_zero_of_not_injective B f
    (by simpa only [Finset.mem_filter_univ] using hf), mul_zero]

end Matrix
