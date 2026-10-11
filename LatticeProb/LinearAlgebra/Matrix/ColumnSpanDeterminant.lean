/-
Determinant-preserving root-column changes and their actual permutation signs.
-/

import LatticeProb.LinearAlgebra.Matrix.RootColumnExpansion
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned



namespace Matrix
open scoped Classical BigOperators
noncomputable section

/-- Adding combinations of the initial columns to the final columns preserves determinant. -/
theorem det_fromCols_add_mul {R a b : Type*} [CommRing R]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : Matrix (a ⊕ b) a R) (U : Matrix (a ⊕ b) b R) (D : Matrix a b R) :
    (fromCols A (U + A * D)).det = (fromCols A U).det := by
  calc
    (fromCols A (U + A * D)).det =
        (fromCols A U * fromBlocks (1 : Matrix a a R) D 0 (1 : Matrix b b R)).det := by
      rw [fromCols_mul_fromBlocks]
      simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, add_comm]
    _ = (fromCols A U).det := by
      rw [det_mul, det_fromBlocks_zero₂₁, det_one, det_one, one_mul, mul_one]

/-- Permuting only the final columns contributes precisely that permutation's sign. -/
theorem det_fromCols_permute_right {R a b : Type*} [CommRing R]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : Matrix (a ⊕ b) a R) (U : Matrix (a ⊕ b) b R) (π : Equiv.Perm b) :
    (fromCols A (U.submatrix id π)).det =
      ((Equiv.Perm.sign π : ℤ) : R) * (fromCols A U).det := by
  have hm : fromCols A (U.submatrix id π) =
      (fromCols A U).submatrix id (Equiv.sumCongr (Equiv.refl a) π) := by
    ext x j
    cases j <;> rfl
  rw [hm, det_permute']
  simp only [Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, one_mul]

/-- The sum-indexed root augmentation is the ordered augmentation under the same two transports. -/
theorem det_fromCols_ordered_roots {R : Type*} [CommRing R] {d k : ℕ}
    (A : Matrix (Fin (d + k)) (Fin d) R)
    (I : Finset (Fin (d + k))) (hI : I.card = k) :
    (fromCols (A.submatrix finSumFinEquiv id)
      (fun x r => if finSumFinEquiv x = I.orderEmbOfFin hI r then (1 : R) else 0)).det =
      (appendRootColumns A I hI).det := by
  have hm : fromCols (A.submatrix finSumFinEquiv id)
      (fun x r => if finSumFinEquiv x = I.orderEmbOfFin hI r then (1 : R) else 0) =
      (appendRootColumns A I hI).submatrix finSumFinEquiv finSumFinEquiv := by
    ext x j
    cases j with
    | inl j => simp only [fromCols_apply_inl, submatrix_apply, finSumFinEquiv_apply_left,
        appendRootColumns_castAdd, id_eq]
    | inr r => simp only [fromCols_apply_inr, submatrix_apply, finSumFinEquiv_apply_right,
        appendRootColumns_natAdd]
  rw [hm, det_submatrix_equiv_self]

/-- **Determinants under column additions.** Matched root differences in the integer edge span determine the actual augmentation sign. -/
theorem det_appendRootColumns_of_matched_span {d k : ℕ}
    (A : Matrix (Fin (d + k)) (Fin d) ℤ)
    (I J : Finset (Fin (d + k))) (hI : I.card = k) (hJ : J.card = k)
    (π : Equiv.Perm (Fin k))
    (hspan : ∀ r, (fun x => (if x = J.orderEmbOfFin hJ (π r) then (1 : ℤ) else 0) -
      (if x = I.orderEmbOfFin hI r then 1 else 0)) ∈
        Submodule.span ℤ (Set.range A.col)) :
    (appendRootColumns A I hI).det =
      (Equiv.Perm.sign π : ℤ) * (appendRootColumns A J hJ).det := by
  have hc : ∀ r, ∃ v : Fin d → ℤ, A.mulVec v =
      (fun x => (if x = J.orderEmbOfFin hJ (π r) then (1 : ℤ) else 0) -
        (if x = I.orderEmbOfFin hI r then 1 else 0)) := by
    intro r
    have hr := hspan r
    rw [← range_mulVecLin] at hr
    exact hr
  choose v hv using hc
  let A' := A.submatrix finSumFinEquiv id
  let U : Matrix (Fin d ⊕ Fin k) (Fin k) ℤ :=
    fun x r => if finSumFinEquiv x = I.orderEmbOfFin hI r then 1 else 0
  let W : Matrix (Fin d ⊕ Fin k) (Fin k) ℤ :=
    fun x r => if finSumFinEquiv x = J.orderEmbOfFin hJ r then 1 else 0
  let D : Matrix (Fin d) (Fin k) ℤ := fun j r => v r j
  have hchange : W.submatrix id π = U + A' * D := by
    ext x r
    have h := congrFun (hv r) (finSumFinEquiv x)
    change (∑ j, A (finSumFinEquiv x) j * v r j) = _ at h
    change (if finSumFinEquiv x = J.orderEmbOfFin hJ (π r) then (1 : ℤ) else 0) =
      (if finSumFinEquiv x = I.orderEmbOfFin hI r then 1 else 0) +
        ∑ j, A (finSumFinEquiv x) j * v r j
    exact (eq_sub_iff_add_eq.mp h).symm.trans (add_comm _ _)
  have hdet : (fromCols A' (W.submatrix id π)).det = (fromCols A' U).det := by
    rw [hchange]
    exact det_fromCols_add_mul A' U D
  rw [det_fromCols_permute_right] at hdet
  have hi := det_fromCols_ordered_roots A I hI
  have hj := det_fromCols_ordered_roots A J hJ
  change (fromCols A' U).det = _ at hi
  change (fromCols A' W).det = _ at hj
  rw [hi, hj] at hdet
  exact hdet.symm

end
end Matrix
