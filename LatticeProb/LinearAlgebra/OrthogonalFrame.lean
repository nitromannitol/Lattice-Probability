module

/-
Finite Euclidean vector families give rectangular real matrices whose Gram
matrix records inner products and whose outer product reconstructs the sum
of coordinate projections. Cross-orthogonal families can be concatenated.
-/
public import LatticeProb.LinearAlgebra.ProjectionFiltration
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

namespace LatticeProb.ProjectionFiltration

open scoped BigOperators InnerProductSpace Matrix
open WithLp

variable {E I : Type*} [Fintype E]

/-- The rectangular matrix with the given Euclidean vectors as its columns. -/
noncomputable def columnFrame (v : I → EuclideanSpace ℝ E) : Matrix E I ℝ :=
  fun e i => v i e

/-- The Gram matrix of a column frame is the matrix of pairwise inner products. -/
theorem transpose_mul_columnFrame (v : I → EuclideanSpace ℝ E) (i j : I) :
    ((columnFrame v).transpose * columnFrame v) i j = inner ℝ (v i) (v j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, columnFrame, PiLp.inner_apply,
    Real.inner_apply]

/-- An orthonormal family gives a rectangular matrix with identity Gram matrix. -/
theorem transpose_mul_columnFrame_eq_one [DecidableEq I]
    {v : I → EuclideanSpace ℝ E} (hv : Orthonormal ℝ v) :
    (columnFrame v).transpose * columnFrame v = 1 := by
  ext i j
  rw [transpose_mul_columnFrame, orthonormal_iff_ite.mp hv]
  rfl

/-- The outer product of the column matrix represents the coordinate projection sum. -/
theorem toEuclideanLin_columnFrame_mul_transpose [DecidableEq E] [Fintype I]
    (v : I → EuclideanSpace ℝ E) :
    (columnFrame v * (columnFrame v).transpose).toEuclideanLin =
      projectionSum v Finset.univ := by
  have hm : columnFrame v * (columnFrame v).transpose =
      ∑ i, Matrix.vecMulVec (ofLp (v i)) (ofLp (v i)) := by
    ext e f
    simp only [Matrix.mul_apply, Matrix.transpose_apply, columnFrame, Matrix.sum_apply,
      Matrix.vecMulVec_apply]
  rw [hm, map_sum]
  simp only [projectionSum]
  apply Finset.sum_congr rfl
  intro i _
  apply Matrix.toEuclideanLin.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  simpa only [rankOneProjection, star_trivial] using
    (InnerProductSpace.symm_toEuclideanLin_rankOne (v i) (v i)).symm

/-- Deleting leading columns from an orthonormal column matrix preserves
orthonormality of the trailing columns on the original finite row carrier. -/
theorem transpose_mul_trailing_columns_eq_one [DecidableEq E] {k m : ℕ}
    (U : Matrix E (Fin (k + m)) ℝ) (hU : U.transpose * U = 1) :
    (U.submatrix id (fun j : Fin k => (⟨m + j.val, by omega⟩ : Fin (k + m)))).transpose *
      U.submatrix id (fun j : Fin k => (⟨m + j.val, by omega⟩ : Fin (k + m))) = 1 := by
  let t : Fin k → Fin (k + m) := fun j => ⟨m + j.val, by omega⟩
  have ht : Function.Injective t := by
    intro i j h
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val h)
  have h : (U.transpose * U).submatrix t t = 1 := by
    rw [hU, Matrix.submatrix_one _ ht]
  rw [← Matrix.submatrix_mul_equiv U.transpose U t (Equiv.refl E) t] at h
  exact h

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Cross-orthogonal orthonormal families remain orthonormal when concatenated. -/
theorem orthonormal_append {m k : ℕ} {v : Fin m → V} {w : Fin k → V}
    (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (hcross : ∀ i j, inner ℝ (v i) (w j) = 0) :
    Orthonormal ℝ (Fin.append v w) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  cases i using Fin.addCases with
  | left i =>
    cases j using Fin.addCases with
    | left j => simp only [Fin.append_left, orthonormal_iff_ite.mp hv,
        Fin.castAdd_inj]
    | right j =>
      have hij : Fin.castAdd k i ≠ Fin.natAdd m j := by
        intro h
        have he := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at he
        omega
      simp only [Fin.append_left, Fin.append_right, hcross, if_neg hij]
  | right i =>
    cases j using Fin.addCases with
    | left j =>
      rw [Fin.append_right, Fin.append_left, real_inner_comm, hcross]
      have hij : Fin.natAdd m i ≠ Fin.castAdd k j := by
        intro h
        have he := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at he
        omega
      rw [if_neg hij]
    | right j => simp only [Fin.append_right, orthonormal_iff_ite.mp hw,
        Fin.natAdd_inj]

/-- **Concatenated projection sum.** The coordinate projections of an appended
family sum to the two original coordinate projection sums. -/
theorem projectionSum_append {m k : ℕ} (v : Fin m → V) (w : Fin k → V) :
    projectionSum (Fin.append v w) Finset.univ =
      projectionSum v Finset.univ + projectionSum w Finset.univ := by
  simp only [projectionSum]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

end LatticeProb.ProjectionFiltration
