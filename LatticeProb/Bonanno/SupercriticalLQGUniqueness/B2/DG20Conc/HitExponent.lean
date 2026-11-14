/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.HitExponent at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
def hitExponent (ξ Q : ℝ) : ℝ :=
  if ξ ≤ Q then ξ * Q - ξ ^ 2 / 2 else Q ^ 2 / 2

 


theorem hitExponent_pos {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q) :
    0 < hitExponent ξ Q := by
  unfold hitExponent
  split_ifs with h
  · have hprod : ξ ^ 2 ≤ ξ * Q := by nlinarith [mul_nonneg hξ.le (sub_nonneg.mpr h)]
    nlinarith [sq_pos_of_pos hξ]
  · positivity

 
end SupercriticalLQGUniqueness.B2.DG20Conc
