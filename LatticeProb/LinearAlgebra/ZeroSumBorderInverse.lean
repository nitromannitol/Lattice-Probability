/-
# Inverse of a zero-sum matrix border

The inverse of a grounded principal matrix is extended by zero at the ground.
Replacing the ground row by a coordinate unit row makes an invertible full
matrix. Its inverse has a constant ground column, and every other column is
the extended grounded inverse minus its value at the pinning vertex.
The proof multiplies the displayed inverse by the border explicitly.
-/
import LatticeProb.LinearAlgebra.ZeroSumBorder



namespace LatticeProb.LinearAlgebra

open Matrix
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The grounded principal inverse extended by zero in the ground row and
column. The inverse formulas using this extension assume that the grounded
principal determinant is a unit. If that determinant is not a unit,
Mathlib's matrix inverse, and hence this extension, is zero. -/
noncomputable def groundInverseExtension (L : Matrix ι ι R) (r : ι) : Matrix ι ι R :=
  fun x y => if hx : x = r then 0 else if hy : y = r then 0 else
    (L.submatrix (fun z : {z : ι // z ≠ r} => z.val) (fun z : {z : ι // z ≠ r} => z.val))⁻¹ ⟨x, hx⟩ ⟨y, hy⟩

/-- The extended grounded inverse vanishes in its ground row. -/
theorem groundInverseExtension_ground_row (L : Matrix ι ι R) (r y : ι) :
    groundInverseExtension L r r y = 0 := by
  simp only [groundInverseExtension, dif_pos]

/-- The extended grounded inverse vanishes in its ground column. -/
theorem groundInverseExtension_ground_column (L : Matrix ι ι R) (r x : ι) :
    groundInverseExtension L r x r = 0 := by
  by_cases hx : x = r
  · simp only [groundInverseExtension, dif_pos hx]
  · simp only [groundInverseExtension, dif_neg hx, dif_pos]

/-- Away from the ground, the extension is the genuine grounded inverse. -/
theorem groundInverseExtension_apply (L : Matrix ι ι R) (r : ι)
    (x y : {z : ι // z ≠ r}) :
    groundInverseExtension L r x.val y.val =
      (L.submatrix (fun z : {z : ι // z ≠ r} => z.val) (fun z : {z : ι // z ≠ r} => z.val))⁻¹ x y := by
  simp only [groundInverseExtension, dif_neg x.prop, dif_neg y.prop]

/-- **Inverse of the zero-sum border.** Replacing the ground row of `L` by
the unit row at `t` gives an inverse whose ground column is one. Every other
column is the grounded inverse extension minus its row at `t`. Only the
whole grounded determinant is assumed invertible. -/
theorem inv_updateRow_single_of_row_sum_zero (L : Matrix ι ι R)
    (hs : ∀ i, ∑ j, L i j = 0) (r t : ι)
    (hM : IsUnit (L.submatrix (fun z : {z : ι // z ≠ r} => z.val) (fun z : {z : ι // z ≠ r} => z.val)).det) :
    (L.updateRow r (Pi.single t 1))⁻¹ =
      fun x y => if y = r then 1 else
        groundInverseExtension L r x y - groundInverseExtension L r t y := by
  let M := L.submatrix (fun z : {z : ι // z ≠ r} => z.val) (fun z : {z : ι // z ≠ r} => z.val)
  let K := groundInverseExtension L r
  let W : Matrix ι ι R := fun x y => if y = r then 1 else K x y - K t y
  have hmul : L.updateRow r (Pi.single t 1) * W = 1 := by
    ext x y
    by_cases hx : x = r
    · subst x
      simp only [Matrix.mul_apply, Matrix.updateRow_self, Pi.single_apply]
      simp only [ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, W, Matrix.one_apply]
      by_cases hy : y = r
      · simp only [hy, if_true]
      · simp only [hy, Ne.symm hy, if_false, sub_self]
    · simp only [Matrix.mul_apply, Matrix.updateRow_ne hx]
      by_cases hy : y = r
      · subst y
        simp only [W, if_true, mul_one, hs, Matrix.one_apply, hx, if_false]
      · simp only [W, hy, if_false, mul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_mul, hs, zero_mul, sub_zero]
        rw [Fintype.sum_eq_add_sum_subtype_ne (fun z => L x z * K z y) r]
        simp only [K, groundInverseExtension_ground_row, mul_zero, zero_add]
        have hm := congrArg (fun A : Matrix {z : ι // z ≠ r} {z : ι // z ≠ r} R =>
          A ⟨x, hx⟩ ⟨y, hy⟩) (Matrix.mul_nonsing_inv M hM)
        have hext (z : {z : ι // z ≠ r}) :
            groundInverseExtension L r z.val y = M⁻¹ z ⟨y, hy⟩ :=
          groundInverseExtension_apply L r z ⟨y, hy⟩
        simp only [hext]
        simpa only [Matrix.mul_apply, M, Matrix.submatrix_apply,
          Matrix.one_apply, Subtype.mk.injEq] using hm
  exact Matrix.inv_eq_right_inv hmul

end LatticeProb.LinearAlgebra
