/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFSchur at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef

 





set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]
  (A : Matrix m m ℝ) (B : Matrix m n ℝ)
  (C : Matrix n m ℝ) (D : Matrix n n ℝ)

 


theorem dgff_schur_cross_zero [Invertible A]
    [Invertible (D - C * ⅟A * B)]
    [Invertible (fromBlocks A B C D)] :
    (⅟(fromBlocks A B C D)).toBlocks₁₂ +
      ⅟A * B * (⅟(fromBlocks A B C D)).toBlocks₂₂ = 0 := by
  rw [Matrix.invOf_fromBlocks₁₁_eq A B C D]
  simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂]
  simp

 

theorem dgff_schur_inner_covariance [Invertible A]
    [Invertible (D - C * ⅟A * B)]
    [Invertible (fromBlocks A B C D)] :
    (⅟(fromBlocks A B C D)).toBlocks₁₁ +
      ⅟A * B * (⅟(fromBlocks A B C D)).toBlocks₂₁ = ⅟A := by
  rw [Matrix.invOf_fromBlocks₁₁_eq A B C D]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁]
  simp [Matrix.mul_assoc]

end SupercriticalLQGUniqueness.B2.QPos
