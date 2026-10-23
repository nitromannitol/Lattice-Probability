import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Module

/-!
# Exponentials of bounded transition operators

The scalar identity part of a bounded generator can be separated from its transition
operator before evaluation. These identities are proved on an abstract normed space,
so their applications do not unfold the implementation of bounded observables.
-/

namespace LatticeProb.JumpChain

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scalar multiplication of an endomorphism commutes with taking its natural powers. -/
theorem operator_smul_pow_apply (A : E →L[ℝ] E) (r : ℝ) (n : ℕ) (v : E) :
    ((r • A) ^ n) v = r ^ n • (A ^ n) v := by
  rw [smul_pow]
  rfl

/-- Separate the scalar identity from the exponential of a bounded generator. -/
theorem exp_smul_sub_one [CompleteSpace E] (A : E →L[ℝ] E) (r : ℝ) :
    NormedSpace.exp (r • (A - 1)) = Real.exp (-r) • NormedSpace.exp (r • A) := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hsplit : r • (A - 1) = (-r) • (1 : E →L[ℝ] E) + r • A := by
    module
  have hcomm : Commute ((-r) • (1 : E →L[ℝ] E)) (r • A) :=
    ((Commute.one_left A).smul_left (-r)).smul_right r
  have hexp : NormedSpace.exp ((-r) • (1 : E →L[ℝ] E)) = Real.exp (-r) • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := E →L[ℝ] E) (-r)).symm
  rw [hsplit, NormedSpace.exp_add_of_commute hcomm, hexp, smul_mul_assoc, one_mul]

end

end LatticeProb.JumpChain
