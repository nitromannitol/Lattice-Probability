module

/-
# Determinant coefficients under independent index permutations

Permuting rows and columns multiplies each polynomial determinant coefficient
by the product of the two permutation signs. Determinant permutation identities
and coefficient extraction through constant multiplication prove the formula.
-/
public import LatticeProb.LinearAlgebra.DeterminantCoefficient

@[expose] public section



namespace LatticeProb.LinearAlgebra

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- **Determinant coefficient covariance.** Independently permuting rows
and columns multiplies each coefficient by both literal integer signs cast
to the coefficient ring. Empty matrices and zero coefficients are allowed. -/
theorem det_submatrix_perms_coeff (A : Matrix ι ι (Polynomial R))
    (α β : Equiv.Perm ι) (n : ℕ) :
    (A.submatrix α β).det.coeff n =
      ((Equiv.Perm.sign α : ℤ) : R) * ((Equiv.Perm.sign β : ℤ) : R) * A.det.coeff n := by
  have h : A.submatrix α β = (A.submatrix α id).submatrix id β := rfl
  rw [h, Matrix.det_permute', Matrix.det_permute]
  rw [← Polynomial.C_eq_intCast, ← Polynomial.C_eq_intCast,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  ring

end LatticeProb.LinearAlgebra
