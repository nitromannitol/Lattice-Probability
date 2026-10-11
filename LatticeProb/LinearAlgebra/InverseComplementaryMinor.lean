/-
# Complementary minors of an inverse matrix

The determinant of a block of a matrix inverse times the whole determinant
is the complementary block determinant. Multiplying by a block triangular
matrix built from the inverse proves the identity without assuming that
any proper block is invertible.
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement



namespace LatticeProb.LinearAlgebra

open Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommRing R]

/-- **Inverse complementary block identity.** If `M` is invertible, the
bottom right block of its inverse has determinant times `det M` equal to the
top left block determinant. Neither proper block needs to be invertible;
empty blocks are allowed. -/
theorem det_inverse_toBlocks₂₂_mul_det (M : Matrix (m ⊕ n) (m ⊕ n) R)
    (hM : IsUnit M.det) :
    M⁻¹.toBlocks₂₂.det * M.det = M.toBlocks₁₁.det := by
  have hinv :
      fromBlocks M⁻¹.toBlocks₁₁ M⁻¹.toBlocks₁₂ M⁻¹.toBlocks₂₁ M⁻¹.toBlocks₂₂ *
        fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = 1 := by
    simpa only [fromBlocks_toBlocks] using M.nonsing_inv_mul hM
  rw [fromBlocks_multiply] at hinv
  have h21 := congrArg Matrix.toBlocks₂₁ hinv
  have h22 := congrArg Matrix.toBlocks₂₂ hinv
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, ← fromBlocks_one] at h21 h22
  have hmul :
      fromBlocks (1 : Matrix m m R) 0 M⁻¹.toBlocks₂₁ M⁻¹.toBlocks₂₂ * M =
      fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 (1 : Matrix n n R) := by
    calc
      _ = fromBlocks (1 : Matrix m m R) 0 M⁻¹.toBlocks₂₁ M⁻¹.toBlocks₂₂ *
          fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ := by
        rw [fromBlocks_toBlocks]
      _ = _ := by
        rw [fromBlocks_multiply]
        simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, h21, h22]
  have hd := congrArg Matrix.det hmul
  simp only [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one,
    one_mul, mul_one] at hd
  exact hd

/-- Complementary inverse minors with independently chosen row and column
orders. The inverse uses the reversed orders, as required for nonprincipal
minors; the whole determinant retains both orders. -/
theorem det_inverse_submatrix_complement_mul_det {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (hM : IsUnit M.det)
    (e f : (m ⊕ n) ≃ ι) :
    (M⁻¹.submatrix (fun i => f (Sum.inr i)) (fun j => e (Sum.inr j))).det *
      (M.submatrix e f).det =
    (M.submatrix (fun i => e (Sum.inl i)) (fun j => f (Sum.inl j))).det := by
  have hN : IsUnit (M.submatrix e f).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      ((Matrix.isUnit_submatrix_equiv e f).mpr ((Matrix.isUnit_iff_isUnit_det M).mpr hM))
  have hd := det_inverse_toBlocks₂₂_mul_det (M.submatrix e f) hN
  rw [Matrix.inv_submatrix_equiv] at hd
  exact hd

/-- The determinant of independently reordered rows and columns records the
sign of their relative permutation. -/
theorem det_submatrix_equiv_eq_sign_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (e f : (m ⊕ n) ≃ ι) :
    (M.submatrix e f).det =
      ((Equiv.Perm.sign (f.trans e.symm) : ℤ) : R) * M.det := by
  have h : M.submatrix e f = (M.submatrix e e).submatrix id (f.trans e.symm) := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [h, Matrix.det_permute', Matrix.det_submatrix_equiv_self]

/-- **Signed complementary inverse-minor identity.** The relative permutation
of the two full orders supplies the exact sign; no proper-minor nonzero
hypothesis is required. -/
theorem det_inverse_submatrix_complement_mul_det_eq_sign {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (hM : IsUnit M.det)
    (e f : (m ⊕ n) ≃ ι) :
    (M⁻¹.submatrix (fun i => f (Sum.inr i)) (fun j => e (Sum.inr j))).det * M.det =
      ((Equiv.Perm.sign (f.trans e.symm) : ℤ) : R) *
        (M.submatrix (fun i => e (Sum.inl i)) (fun j => f (Sum.inl j))).det := by
  have hd := det_inverse_submatrix_complement_mul_det M hM e f
  rw [det_submatrix_equiv_eq_sign_mul] at hd
  let s : R := ((Equiv.Perm.sign (f.trans e.symm) : ℤ) : R)
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  calc
    _ = (M⁻¹.submatrix (fun i => f (Sum.inr i)) (fun j => e (Sum.inr j))).det *
        ((s * s) * M.det) := by rw [hs, one_mul]
    _ = s * ((M⁻¹.submatrix (fun i => f (Sum.inr i))
        (fun j => e (Sum.inr j))).det * (s * M.det)) := by ring
    _ = _ := congrArg (fun t : R => s * t) hd

/-- Over a field, the signed complementary minor divided by the original
whole determinant is the corresponding inverse minor. Only the whole
matrix's invertibility is assumed. -/
theorem det_inverse_submatrix_complement_eq_div {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (hM : IsUnit M.det)
    (e f : (m ⊕ n) ≃ ι) :
    (M⁻¹.submatrix (fun i => f (Sum.inr i)) (fun j => e (Sum.inr j))).det =
      (((Equiv.Perm.sign (f.trans e.symm) : ℤ) : K) *
        (M.submatrix (fun i => e (Sum.inl i)) (fun j => f (Sum.inl j))).det) / M.det :=
  (eq_div_iff hM.ne_zero).mpr
    (det_inverse_submatrix_complement_mul_det_eq_sign M hM e f)

end LatticeProb.LinearAlgebra
