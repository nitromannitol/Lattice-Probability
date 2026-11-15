import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients

/-! # Quarter-turn invariant planar covariance matrices -/

set_option autoImplicit false

open scoped NNReal

namespace LatticeProb

/-- The matrix of a counterclockwise quarter turn in the standard basis. -/
def planarQuarterTurn : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- A symmetric positive-definite planar matrix invariant under a quarter turn
is a positive multiple of the identity. -/
theorem exists_pos_smul_one_of_quarterTurn_invariant
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ReflectedGMS.StatementIngredients.SymmetricPositiveDefinite A)
    (hrot : planarQuarterTurn * A * planarQuarterTurn.transpose = A) :
    ∃ c : ℝ≥0, 0 < c ∧ A = (c : ℝ) • 1 := by
  have hdiag : A 1 1 = A 0 0 := by
    have h := congrFun (congrFun hrot 0) 0
    simpa [planarQuarterTurn, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h
  have hoff : -A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hrot 0) 1
    simpa [planarQuarterTurn, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h
  have hsym := hA.1 0 1
  have hoffzero : A 0 1 = 0 := by linarith
  have hpos : 0 < A 0 0 := by
    have hv : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
      intro h
      have := congrFun h 0
      norm_num at this
    have h := hA.2 ![1, 0] hv
    simpa [Fin.sum_univ_two] using h
  refine ⟨⟨A 0 0, hpos.le⟩, hpos, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hdiag, hoffzero, ← hsym] <;> rfl

end LatticeProb
