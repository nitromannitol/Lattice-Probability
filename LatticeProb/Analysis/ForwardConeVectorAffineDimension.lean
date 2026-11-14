import LatticeProb.Analysis.ForwardConeVectorTimeChangeDimension
import LatticeProb.Analysis.ConeVectorAmplitudeScaling

/-! # Affine rescaling of forward cone-vector dimension -/

set_option autoImplicit false

open Set MeasureTheory
open scoped NNReal

namespace LatticeProb

/-- Affine time rescaling and positive coordinate normalization transfer a
forward cone-vector dimension bound from the negative unit interval. -/
theorem dimH_forwardConeVectors_interval_le_affine
    (X Y : ℝ → ℝ) {a b c d : ℝ} (hab : a < b) (hc : 0 < c) (hd : 0 < d)
    (hne : ∀ s ∈ Ioo a b,
      ∃ t > s, (∃ r ∈ Icc s t, X r < X s) ∧
        (∃ r ∈ Icc s t, Y r < Y s)) :
    dimH {z : ℝ × ℝ | z ∈ forwardConeVectors X Y ∧ a < z.2 ∧ z.1 < b} ≤
      dimH {z : ℝ × ℝ | z ∈ forwardConeVectors
        (fun t => c * (X (b + (b - a) * t) - X b))
        (fun t => d * (Y (b + (b - a) * t) - Y b)) ∧
        -1 < z.2 ∧ z.1 < 0} := by
  have hp : 0 < b - a := sub_pos.mpr hab
  let e : ℝ ≃o ℝ := (OrderIso.mulLeft₀ (b - a) hp).trans (OrderIso.addLeft b)
  have heval (t : ℝ) : e t = b + (b - a) * t := rfl
  have he : LipschitzWith ⟨b - a, le_of_lt hp⟩ e := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [heval, Real.dist_eq]
    rw [show (b + (b - a) * x) - (b + (b - a) * y) =
      (b - a) * (x - y) by ring, abs_mul, abs_of_pos hp]
    exact le_rfl
  have hneg : e (-1) = a := by rw [heval]; ring
  have hzero : e 0 = b := by simp only [heval, mul_zero, add_zero]
  have h := dimH_forwardConeVectors_interval_le_timeChange X Y e (X b) (Y b) he (by
    simpa only [hneg, hzero] using hne)
  rw [forwardConeVectors_mul_pos _ _ hc hd]
  simpa only [hneg, hzero, heval] using h

/-- The preceding estimate with the square-root normalization used for
Brownian paths. -/
theorem dimH_forwardConeVectors_interval_le_sqrt_rescale
    (X Y : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hne : ∀ s ∈ Ioo a b,
      ∃ t > s, (∃ r ∈ Icc s t, X r < X s) ∧
        (∃ r ∈ Icc s t, Y r < Y s)) :
    dimH {z : ℝ × ℝ | z ∈ forwardConeVectors X Y ∧ a < z.2 ∧ z.1 < b} ≤
      dimH {z : ℝ × ℝ | z ∈ forwardConeVectors
        (fun t => (Real.sqrt (b - a))⁻¹ * (X (b + (b - a) * t) - X b))
        (fun t => (Real.sqrt (b - a))⁻¹ * (Y (b + (b - a) * t) - Y b)) ∧
        -1 < z.2 ∧ z.1 < 0} := by
  exact dimH_forwardConeVectors_interval_le_affine X Y hab
    (inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hab)))
    (inv_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hab))) hne

end LatticeProb
