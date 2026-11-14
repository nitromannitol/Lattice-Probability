import LatticeProb.Analysis.ConeVectorTimeChangeDimension
import LatticeProb.Analysis.ConeVectorAmplitudeScaling

/-! # Affine rescaling of backward cone-vector dimension -/

set_option autoImplicit false

open Set MeasureTheory
open scoped NNReal

namespace LatticeProb

/-- Affine time rescaling and positive coordinate normalization transfer a
backward cone-vector dimension bound from the unit interval to any interval. -/
theorem dimH_backwardConeVectors_interval_le_affine
    (X Y : ℝ → ℝ) {a b c d : ℝ} (hab : a < b) (hc : 0 < c) (hd : 0 < d)
    (hne : ∀ s ∈ Ioo a b,
      ∃ t < s, (∃ r ∈ Icc t s, X r < X s) ∧
        (∃ r ∈ Icc t s, Y r < Y s)) :
    dimH {z : ℝ × ℝ | z ∈ backwardConeVectors X Y ∧ a < z.1 ∧ z.2 < b} ≤
      dimH {z : ℝ × ℝ | z ∈ backwardConeVectors
        (fun t => c * (X (a + (b - a) * t) - X a))
        (fun t => d * (Y (a + (b - a) * t) - Y a)) ∧
        0 < z.1 ∧ z.2 < 1} := by
  have hp : 0 < b - a := sub_pos.mpr hab
  let e : ℝ ≃o ℝ := (OrderIso.mulLeft₀ (b - a) hp).trans (OrderIso.addLeft a)
  have heval (t : ℝ) : e t = a + (b - a) * t := rfl
  have he : LipschitzWith ⟨b - a, le_of_lt hp⟩ e := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [heval, Real.dist_eq]
    rw [show (a + (b - a) * x) - (a + (b - a) * y) =
      (b - a) * (x - y) by ring, abs_mul, abs_of_pos hp]
    exact le_rfl
  have h := dimH_backwardConeVectors_interval_le_timeChange X Y e (X a) (Y a) he (by
    simpa only [heval, mul_zero, add_zero, mul_one, add_sub_cancel] using hne)
  rw [backwardConeVectors_mul_pos _ _ hc hd]
  simpa only [heval, mul_zero, add_zero, mul_one, add_sub_cancel] using h

/-- The preceding estimate with the square-root normalization used for
Brownian paths. -/
theorem dimH_backwardConeVectors_interval_le_sqrt_rescale
    (X Y : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hne : ∀ s ∈ Ioo a b,
      ∃ t < s, (∃ r ∈ Icc t s, X r < X s) ∧
        (∃ r ∈ Icc t s, Y r < Y s)) :
    dimH {z : ℝ × ℝ | z ∈ backwardConeVectors X Y ∧ a < z.1 ∧ z.2 < b} ≤
      dimH {z : ℝ × ℝ | z ∈ backwardConeVectors
        (fun t => (Real.sqrt (b - a))⁻¹ * (X (a + (b - a) * t) - X a))
        (fun t => (Real.sqrt (b - a))⁻¹ * (Y (a + (b - a) * t) - Y a)) ∧
        0 < z.1 ∧ z.2 < 1} := by
  exact dimH_backwardConeVectors_interval_le_affine X Y hab
    (inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hab)))
    (inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hab))) hne

end LatticeProb
