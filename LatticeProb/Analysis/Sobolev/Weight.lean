import LatticeProb.Analysis.Sobolev.Basic

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The pointwise weight comparison behind the high-frequency bound: on
`Λ ≤ ‖ξ‖` the weight at `s₀` is at most `(1 + (2πΛ)²)^{s₀ - s}` times the
weight at `s`, for `s₀ ≤ s`. -/
theorem weight_le {d : ℕ} {s₀ s Λ : ℝ} (h : s₀ ≤ s) (hΛ : 0 ≤ Λ)
    {ξ : Space d} (hξ : Λ ≤ ‖ξ‖) :
    (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
      ≤ (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s) * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
  have hbase : (1 : ℝ) ≤ 1 + (2 * Real.pi * Λ) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.pi * Λ)]
  have hpos : (0 : ℝ) < 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]
  have hmono : (1 + (2 * Real.pi * Λ) ^ 2) ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) := by
    have h2 : (2 * Real.pi * Λ) ≤ (2 * Real.pi * ‖ξ‖) := by
      have := mul_le_mul_of_nonneg_left hξ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      linarith
    nlinarith [sq_nonneg (2 * Real.pi * Λ), sq_nonneg (2 * Real.pi * ‖ξ‖),
      mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Λ) h2]
  have hpow : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
      ≤ (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hmono (by linarith)
  have hsplit : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
      = (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
    rw [← Real.rpow_add hpos]; ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hpow (le_of_lt (Real.rpow_pos_of_pos hpos s))

end LatticeProb.Sobolev
