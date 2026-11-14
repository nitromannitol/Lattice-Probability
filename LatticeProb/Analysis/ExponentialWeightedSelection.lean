import Mathlib

/-!
# Selection from an exponentially weighted integral

A small weighted lower integral yields a point where the integrand is small. The comparison
function need not be measurable.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- If an exponentially weighted lower integral is small, the comparison function is small
at some point of the prescribed interval. -/
theorem exists_lt_of_exp_weighted_lintegral_lt {f : ℝ → ℝ≥0∞} {c a b s : ℝ}
    (hca : c ≤ a) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : (∫⁻ r in Ioi c, ENNReal.ofReal (Real.exp (-r)) * min 1 (f r)) <
      ENNReal.ofReal (Real.exp (-b) * s * (b - a))) :
    ∃ r ∈ Ioo a b, f r < ENNReal.ofReal s := by
  by_contra hcon
  have hge : ∀ r ∈ Ioo a b, ENNReal.ofReal s ≤ f r :=
    fun r hr => not_lt.1 fun hlt => hcon ⟨r, hr, hlt⟩
  have hes : 0 ≤ Real.exp (-b) * s := mul_nonneg (Real.exp_pos _).le hs0
  refine (not_le.2 h) ?_
  calc ENNReal.ofReal (Real.exp (-b) * s * (b - a))
      = ENNReal.ofReal (Real.exp (-b) * s) * volume (Ioo a b) := by
        rw [Real.volume_Ioo, ← ENNReal.ofReal_mul hes]
    _ = ∫⁻ _ in Ioo a b, ENNReal.ofReal (Real.exp (-b) * s) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Ioo a b, ENNReal.ofReal (Real.exp (-r)) * min 1 (f r) := by
        refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hr.2]))) ?_
        exact le_min (ENNReal.ofReal_le_one.2 hs1) (hge r hr)
    _ ≤ _ := lintegral_mono_set fun r hr => lt_of_le_of_lt hca hr.1

end LatticeProb
