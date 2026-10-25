module

/-
# Contraction of an appended determinant row

These identities express contraction by a vector in determinant coordinates.
They apply to arbitrary finite index types, including an empty original minor.
-/

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section



namespace LatticeProb.LinearAlgebra
open scoped BigOperators

variable {R I E : Type*} [CommRing R] [Fintype I] [DecidableEq I]

/-- A square matrix with one appended row and column. -/
def borderedMatrix (M : Matrix I I R) (top bottom : I → R) (corner : R) :
    Matrix (I ⊕ Unit) (I ⊕ Unit) R :=
  Matrix.fromBlocks M (fun i _ => top i) (fun _ j => bottom j) (fun _ _ => corner)

/-- The determinant is linear in an arbitrarily indexed finite sum replacing one row. -/
theorem sum_mul_det_update_row (M : Matrix I I R) (i : I) (s : Finset E)
    (c : E → R) (row : E → I → R) :
    (∑ e ∈ s, c e * (M.updateRow i (row e)).det) =
      (M.updateRow i (∑ e ∈ s, c e • row e)).det := by
  calc
    (∑ e ∈ s, c e * (M.updateRow i (row e)).det) =
        ∑ e ∈ s, (M.updateRow i (c e • row e)).det := by
      apply Finset.sum_congr rfl
      intro e _
      exact (Matrix.det_updateRow_smul M i (c e) (row e)).symm
    _ = (M.updateRow i (∑ e ∈ s, c e • row e)).det :=
      (Matrix.detRowAlternating.map_update_sum s i (fun e => c e • row e)
        (fun j => M j)).symm

/-- **Bordered determinant contraction.** Contracting the appended row leaves the original determinant times the
contracted corner, when every contracted original column vanishes. -/
theorem sum_mul_det_bordered_matrix [Fintype E]
    (M : Matrix I I R) (top : I → R) (row : E → I → R) (corner c : E → R)
    (horth : ∀ j, ∑ e, c e * row e j = 0) :
    (∑ e, c e * (borderedMatrix M top (row e) (corner e)).det) =
      M.det * ∑ e, c e * corner e := by
  let B := borderedMatrix M top 0 0
  let lastRow : E → (I ⊕ Unit) → R :=
    fun e => Sum.elim (row e) (fun _ => corner e)
  have hrow (e : E) : B.updateRow (Sum.inr ()) (lastRow e) =
      borderedMatrix M top (row e) (corner e) := by
    ext i j
    cases i with
    | inl i => cases j <;> simp [B, lastRow, borderedMatrix, Matrix.updateRow_apply]
    | inr i => cases i; cases j <;>
        simp [B, lastRow, borderedMatrix, Matrix.updateRow_apply]
  have hsum : (∑ e, c e • lastRow e) =
      Sum.elim (0 : I → R) (fun _ => ∑ e, c e * corner e) := by
    funext j
    cases j with
    | inl j => simpa [lastRow, Finset.sum_apply] using horth j
    | inr j => simp [lastRow, Finset.sum_apply]
  calc
    (∑ e, c e * (borderedMatrix M top (row e) (corner e)).det) =
        ∑ e, c e * (B.updateRow (Sum.inr ()) (lastRow e)).det := by
          simp only [hrow]
    _ = (B.updateRow (Sum.inr ()) (∑ e, c e • lastRow e)).det :=
      sum_mul_det_update_row B (Sum.inr ()) Finset.univ c lastRow
    _ = (borderedMatrix M top 0 (∑ e, c e * corner e)).det := by
      rw [hsum]
      congr 1
      ext i j
      cases i with
      | inl i => cases j <;> simp [B, borderedMatrix, Matrix.updateRow_apply]
      | inr i => cases i; cases j <;>
          simp [B, borderedMatrix, Matrix.updateRow_apply]
    _ = M.det * ∑ e, c e * corner e := by
      calc
        _ = M.det * (Matrix.of fun (_ _ : Unit) => ∑ e, c e * corner e).det :=
          Matrix.det_fromBlocks_zero₂₁ M (fun i _ => top i) _
        _ = _ := congrArg (fun t : R => M.det * t)
          (Matrix.det_unique (Matrix.of fun (_ _ : Unit) => ∑ e, c e * corner e))

end LatticeProb.LinearAlgebra
