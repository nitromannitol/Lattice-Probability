/-
Copyright (c) 2026. All rights reserved.
-/
import LatticeProb.Prob.CrossingTimesClock3

/-!
# Scaling of the crossing clock

The crossing clock `crossClock m f u = limsup_n m 4⁻ⁿ N_n(u)` is homogeneous in the normalising
constant `m`: `crossClock (c * m) f u = c * crossClock m f u` for every finite `c : ℝ≥0∞`.  Consequently,
if the clock with constant `m` is `u ↦ c * u` for a finite `c ≠ 0`, the clock with constant
`c⁻¹ * m` is the identity.
-/

open Filter
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {E : Type*} [PseudoMetricSpace E]

/-- **Homogeneity of the crossing clock in its constant.** -/
theorem crossClock_const_mul {c : ℝ≥0∞} (hc : c ≠ ⊤) (m : ℝ≥0∞) (f : ℝ≥0 → E) (u : ℝ≥0) :
    crossClock (c * m) f u = c * crossClock m f u := by
  unfold crossClock
  rw [← ENNReal.limsup_const_mul_of_ne_top hc]
  congr 1
  funext n
  ring

/-- If the clock of `f` with constant `m` is `u ↦ c * u` (`c` finite, nonzero), the clock with
constant `c⁻¹ * m` is the identity. -/
theorem crossClock_inv_mul_eq_self {c m : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) {f : ℝ≥0 → E}
    (hf : ∀ u : ℝ≥0, crossClock m f u = c * u) (u : ℝ≥0) :
    crossClock (c⁻¹ * m) f u = u := by
  rw [crossClock_const_mul (ENNReal.inv_ne_top.2 hc0), hf, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

end LatticeProb
