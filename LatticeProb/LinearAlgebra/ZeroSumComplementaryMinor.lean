/-
# Complementary minors of zero-sum matrices

Inverse row differences of a grounded matrix give complementary minors of
the full matrix with zero row sums. A coordinate unit row borders the full
matrix; its inverse contains the row differences, and the ordinary signed
Jacobi identity supplies the complementary minor. Independent full orders
retain their literal permutation sign, with no proper-minor invertibility.
-/
import LatticeProb.LinearAlgebra.ZeroSumBorderInverse



namespace LatticeProb.LinearAlgebra

open Matrix
open scoped BigOperators

variable {ι m R : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
  [DecidableEq m] [CommRing R]

/-- **Zero-sum complementary-minor identity.** Ground at the first root of
the row order and subtract the inverse row at the first column root.
The resulting determinant times the grounded determinant is the full
complementary minor with the exact sign of the two full orders. Empty and
singular proper minors are included. -/
theorem det_groundInverseExtension_differences_mul_det {n : ℕ}
    (L : Matrix ι ι R) (hs : ∀ i, ∑ j, L i j = 0)
    (e f : (m ⊕ Fin (n + 1)) ≃ ι)
    (hM : IsUnit (L.submatrix
      (fun z : {z : ι // z ≠ e (Sum.inr 0)} => z.val) Subtype.val).det) :
    (Matrix.of fun i j : Fin n =>
      groundInverseExtension L (e (Sum.inr 0))
        (f (Sum.inr j.succ)) (e (Sum.inr i.succ)) -
      groundInverseExtension L (e (Sum.inr 0))
        (f (Sum.inr 0)) (e (Sum.inr i.succ))).det *
      (L.submatrix (fun z : {z : ι // z ≠ e (Sum.inr 0)} => z.val) Subtype.val).det =
      ((Equiv.Perm.sign (f.trans e.symm) : ℤ) : R) *
        (L.submatrix (fun i : m => e (Sum.inl i)) (fun j : m => f (Sum.inl j))).det := by
  let r := e (Sum.inr 0)
  let t := f (Sum.inr 0)
  let T := L.updateRow r (Pi.single t 1)
  have hd : T.det = (L.submatrix
      (fun z : {z : ι // z ≠ r} => z.val) Subtype.val).det :=
    det_updateRow_single_of_row_sum_zero L hs r t
  have hT : IsUnit T.det := hd.symm ▸ hM
  have hinv := inv_updateRow_single_of_row_sum_zero L hs r t hM
  let A := T⁻¹.submatrix (fun j => f (Sum.inr j)) (fun i => e (Sum.inr i))
  have hrow (j : Fin (n + 1)) : A 0 j = if j = 0 then 1 else 0 := by
    have he : e (Sum.inr j) = r ↔ j = 0 := by
      constructor
      · intro h
        exact Sum.inr.inj (e.injective h)
      · rintro rfl
        rfl
    simp only [A, Matrix.submatrix_apply, T, hinv, he, t, sub_self]
  have hAd : A.det = (A.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_row_zero]
    simp only [hrow, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.val_zero, pow_zero,
      one_mul, Fin.succAbove_zero]
  have hminor : A.submatrix Fin.succ Fin.succ =
      (Matrix.of fun i j : Fin n =>
        groundInverseExtension L r (f (Sum.inr j.succ)) (e (Sum.inr i.succ)) -
          groundInverseExtension L r t (e (Sum.inr i.succ))).transpose := by
    ext i j
    have he : e (Sum.inr j.succ) ≠ r := by
      intro h
      exact Fin.succ_ne_zero j (Sum.inr.inj (e.injective h))
    simp only [A, Matrix.submatrix_apply, T, hinv, he, if_false,
      Matrix.transpose_apply, Matrix.of_apply]
  have hcomp : T.submatrix (fun i : m => e (Sum.inl i))
      (fun j : m => f (Sum.inl j)) =
      L.submatrix (fun i : m => e (Sum.inl i)) (fun j : m => f (Sum.inl j)) := by
    ext i j
    have he : e (Sum.inl i) ≠ r := by
      intro h
      exact Sum.inl_ne_inr (e.injective h)
    simp only [Matrix.submatrix_apply, T, Matrix.updateRow_ne he]
  have hj := det_inverse_submatrix_complement_mul_det_eq_sign T hT e f
  rw [hcomp, ← show A = T⁻¹.submatrix (fun j => f (Sum.inr j))
    (fun i => e (Sum.inr i)) from rfl, hAd, hminor, Matrix.det_transpose, hd] at hj
  exact hj

end LatticeProb.LinearAlgebra
