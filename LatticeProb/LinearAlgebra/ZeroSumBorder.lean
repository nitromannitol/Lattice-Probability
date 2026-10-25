module

/-
# Bordering matrices with zero row sums

Replacing one row of a matrix with zero row sums by a coordinate unit row
preserves its grounded determinant. Adding all columns into the ground
column gives a block triangular matrix, without any condition on proper
minors. This provides an invertible border for complementary-minor identities.
-/
public import LatticeProb.LinearAlgebra.InverseComplementaryMinor

@[expose] public section



namespace LatticeProb.LinearAlgebra

open Matrix
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- **Zero-sum bordering determinant.** Replacing the `r` row by the unit
row at any `t` gives the determinant of the principal matrix deleting `r`.
Only the original row sums must vanish; proper minors may be singular. -/
theorem det_updateRow_single_of_row_sum_zero (L : Matrix ι ι R)
    (hs : ∀ i, ∑ j, L i j = 0) (r t : ι) :
    (L.updateRow r (Pi.single t 1)).det =
      (L.submatrix (fun x : {x : ι // x ≠ r} => x.val) Subtype.val).det := by
  let T := L.updateRow r (Pi.single t 1)
  let N := T.updateCol r (fun i => ∑ j, T i j)
  have hd : N.det = T.det := by
    simpa only [N, one_smul] using Matrix.det_updateCol_sum T r (fun _ => (1 : R))
  let e := Equiv.sumCompl (fun x : ι => x = r)
  have hblock : N.submatrix e e = Matrix.fromBlocks
      (1 : Matrix {x : ι // x = r} {x : ι // x = r} R)
      (T.submatrix (fun x : {x : ι // x = r} => x.val) Subtype.val)
      (0 : Matrix {x : ι // x ≠ r} {x : ι // x = r} R)
      (L.submatrix (fun x : {x : ι // x ≠ r} => x.val) Subtype.val) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have hi : i.val = r := i.prop
      have hj : j.val = r := j.prop
      have he : i = j := Subtype.ext (hi.trans hj.symm)
      simp only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inl,
        Matrix.fromBlocks_apply₁₁, Matrix.one_apply, he, if_true]
      simp only [N, Matrix.updateCol_apply, hj, if_true, T, Matrix.updateRow_apply,
        if_true, Pi.single_apply]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, Matrix.fromBlocks_apply₁₂, N,
        Matrix.updateCol_apply, j.prop, if_false]
    · simp only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inl,
        Equiv.sumCompl_apply_inr, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
        N, Matrix.updateCol_apply, j.prop, if_true, T, Matrix.updateRow_apply,
        i.prop, if_false, hs]
    · simp only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inr,
        Matrix.fromBlocks_apply₂₂, N, Matrix.updateCol_apply, j.prop, if_false,
        T, Matrix.updateRow_apply, i.prop]
  calc
    T.det = N.det := hd.symm
    _ = (N.submatrix e e).det := (Matrix.det_submatrix_equiv_self e N).symm
    _ = _ := by rw [hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

end LatticeProb.LinearAlgebra
