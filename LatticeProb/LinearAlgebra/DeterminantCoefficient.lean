/-
# Linear coefficient of a determinant with a constant parameter matrix

The coefficient of `X` in `det (X + C (M i j))` is the determinant of the
matrix of double differences relative to row and column zero. Subtracting the
first row and then the first column isolates `X` in the upper left entry;
Laplace expansion gives the coefficient. In particular, adding arbitrary row
and column potentials does not change it.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring



namespace LatticeProb.LinearAlgebra

open scoped BigOperators
open Polynomial

variable {R : Type*} [CommRing R]

/-- **Double-difference coefficient formula.** For a nonempty square matrix,
the linear coefficient of `det (X + C (M i j))` is the determinant of its double
differences with respect to the first row and first column. -/
theorem det_X_add_C_coeff_one {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (Matrix.of (fun i j => (X : Polynomial R) + C (M i j))).det.coeff 1 =
      (Matrix.of (fun i j : Fin n =>
        M i.succ j.succ - M 0 j.succ - M i.succ 0 + M 0 0)).det := by
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial R) :=
    fun i j => X + C (M i j)
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial R) :=
    fun i j => Fin.cases (X + C (M 0 j))
      (fun i => C (M i.succ j - M 0 j)) i
  have hQ : Q.det = P.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 0 then 0 else -1) 0
    · exact if_pos rfl
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Q, P, Fin.cases_zero, ite_true, zero_mul, add_zero]
      · simp only [Q, P, Fin.cases_succ, Fin.succ_ne_zero, if_false, neg_one_mul,
          map_sub]
        ring
  let N : Matrix (Fin n) (Fin (n + 1)) R :=
    fun i j => Fin.cases (M i.succ 0 - M 0 0)
      (fun j => M i.succ j.succ - M 0 j.succ - M i.succ 0 + M 0 0) j
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial R) :=
    fun i j => Fin.cases
      (Fin.cases (X + C (M 0 0)) (fun j => C (M 0 j.succ - M 0 0)) j)
      (fun i => C (N i j)) i
  have hT : T.det = Q.det := by
    rw [← Matrix.det_transpose T, ← Matrix.det_transpose Q]
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun j => if j = 0 then 0 else -1) 0
    · exact if_pos rfl
    · intro j i
      change T i j = Q i j + (if j = 0 then 0 else -1) * Q i 0
      refine Fin.cases ?_ (fun j => ?_) j
      · refine Fin.cases ?_ (fun i => ?_) i <;>
          simp only [T, Q, N, Fin.cases_zero, Fin.cases_succ, ite_true,
            zero_mul, add_zero]
      · simp only [Fin.succ_ne_zero, if_false, neg_one_mul]
        refine Fin.cases ?_ (fun i => ?_) i <;>
          simp only [T, Q, N, Fin.cases_zero, Fin.cases_succ, map_sub, map_add] <;> ring
  have hminor (j : Fin (n + 1)) :
      (T.submatrix Fin.succ j.succAbove).det =
        C ((N.submatrix id j.succAbove).det) := by
    rw [RingHom.map_det]
    rfl
  have hcoeff : T.det.coeff 1 =
      (Matrix.of (fun i j : Fin n =>
        M i.succ j.succ - M 0 j.succ - M i.succ 0 + M 0 0)).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp_rw [hminor]
    simp only [T, Fin.cases_zero, Fin.cases_succ, Fin.val_zero, pow_zero, one_mul,
      Polynomial.coeff_add, Polynomial.coeff_mul_C,
      Polynomial.coeff_X, Polynomial.coeff_C, ite_true, if_neg (by decide : 1 ≠ 0),
      add_zero, one_mul]
    have hz : (∑ j : Fin n, (-1 : Polynomial R) ^ (j.succ : ℕ) *
        C (M 0 j.succ - M 0 0) * C ((N.submatrix id j.succ.succAbove).det)).coeff 1 = 0 := by
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro j _
      have he : (-1 : Polynomial R) ^ (j.succ : ℕ) *
          C (M 0 j.succ - M 0 0) * C ((N.submatrix id j.succ.succAbove).det) =
          C ((-1 : R) ^ (j.succ : ℕ) * (M 0 j.succ - M 0 0) *
            (N.submatrix id j.succ.succAbove).det) := by
        simp only [map_mul, map_pow, map_neg, map_one]
      rw [he, Polynomial.coeff_C]
      exact if_neg (by decide : 1 ≠ 0)
    rw [hz, add_zero]
    rfl
  exact (congrArg (fun p : Polynomial R => p.coeff 1) (hT.trans hQ)).symm.trans hcoeff

/-- **Potential-shift invariance.** Adding an arbitrary function of the row
and an arbitrary function of the column leaves the coefficient of `X` in
`det (X + C (M i j))` unchanged, including empty matrices. -/
theorem det_X_add_C_coeff_one_add_row_add_column {k : ℕ}
    (M : Matrix (Fin k) (Fin k) R) (u v : Fin k → R) :
    (Matrix.of (fun i j => (X : Polynomial R) + C (M i j + u i + v j))).det.coeff 1 =
      (Matrix.of (fun i j => (X : Polynomial R) + C (M i j))).det.coeff 1 := by
  cases k with
  | zero => simp only [Matrix.det_fin_zero, Polynomial.coeff_one, one_ne_zero, if_false]
  | succ n =>
    rw [det_X_add_C_coeff_one, det_X_add_C_coeff_one]
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    ring

end LatticeProb.LinearAlgebra
