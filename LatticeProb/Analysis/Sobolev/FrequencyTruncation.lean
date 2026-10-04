/-
# The frequency-truncation operator `P_Λ`

The first missing input of the low-frequency net `rkLowFreqNet`
(`RellichLowFreqNet.lean`) is the frequency-truncation operator
`P_Λ φ = 𝓕⁻ (χ_Λ · 𝓕 φ)`, the Fourier multiplier by a smooth radial cutoff `χ_Λ`
that is `1` on `‖ξ‖ ≤ Λ` and `0` on `‖ξ‖ ≥ 2Λ`.

This module builds it on Schwartz functions from Mathlib's
`SchwartzMap.fourierMultiplierCLM`, proves that its Fourier transform is the
cutoff multiple of `𝓕 φ`, and reads off the two facts the net consumes: `χ_Λ`
lies in `[0, 1]`, and `P_Λ φ` has vanishing Fourier transform beyond `2Λ`, i.e.
it is band-limited.

The remaining inputs of `rkLowFreqNet` — the band-limited Bernstein bound and
the Arzelà–Ascoli net with the support repair — are not touched here.
-/
import LatticeProb.Analysis.Sobolev.BandLimited

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace LatticeProb.Sobolev

/-- The scaled radial bump: `1` on `‖ξ‖ ≤ Λ`, `0` on `‖ξ‖ ≥ 2Λ`, smooth. -/
noncomputable def bandCut (d : ℕ) (Λ : ℝ) : Space d → ℝ :=
  fun ξ => (default : ContDiffBump (0 : Space d)) (Λ⁻¹ • ξ)

/-- The radial cutoff is smooth. -/
theorem bandCut_contDiff (d : ℕ) (Λ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (bandCut d Λ) := by
  unfold bandCut
  exact (default : ContDiffBump (0 : Space d)).contDiff.comp (contDiff_id.const_smul Λ⁻¹)

/-- The radial cutoff has temperate growth, so it is a valid Fourier multiplier. -/
theorem bandCut_temperate (d : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) :
    (bandCut d Λ).HasTemperateGrowth := by
  have hcs : HasCompactSupport (bandCut d Λ) := by
    unfold bandCut
    exact (default : ContDiffBump (0 : Space d)).hasCompactSupport.comp_smul (inv_ne_zero hΛ)
  exact hcs.hasTemperateGrowth (bandCut_contDiff d Λ)

/-- The cutoff takes values in `[0, 1]`. -/
theorem bandCut_nonneg (d : ℕ) (Λ : ℝ) (ξ : Space d) : 0 ≤ bandCut d Λ ξ :=
  (default : ContDiffBump (0 : Space d)).nonneg

/-- The cutoff takes values in `[0, 1]`. -/
theorem bandCut_le_one (d : ℕ) (Λ : ℝ) (ξ : Space d) : bandCut d Λ ξ ≤ 1 :=
  (default : ContDiffBump (0 : Space d)).le_one

/-- The cutoff is `1` on the closed ball of radius `Λ`. -/
theorem bandCut_eq_one (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) {ξ : Space d} (hξ : ‖ξ‖ ≤ Λ) :
    bandCut d Λ ξ = 1 := by
  unfold bandCut
  apply (default : ContDiffBump (0 : Space d)).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity),
    inv_mul_le_iff₀ hΛ]
  have hr : (default : ContDiffBump (0 : Space d)).rIn = 1 := rfl
  rw [hr, mul_one]
  exact hξ

/-- The cutoff is `0` outside the closed ball of radius `2Λ`. -/
theorem bandCut_eq_zero (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) {ξ : Space d}
    (hξ : 2 * Λ ≤ ‖ξ‖) :
    bandCut d Λ ξ = 0 := by
  unfold bandCut
  apply (default : ContDiffBump (0 : Space d)).zero_of_le_dist
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div,
    le_div_iff₀ hΛ]
  have hr : (default : ContDiffBump (0 : Space d)).rOut = 2 := rfl
  rw [hr]; linarith

/-- **The frequency-truncation operator.**  The Fourier multiplier by the radial
cutoff `χ_Λ`: `P_Λ φ = 𝓕⁻ (χ_Λ · 𝓕 φ)`. -/
noncomputable def bandTrunc (d : ℕ) (Λ : ℝ) (_ : Λ ≠ 0) (F : 𝓢(Space d, ℂ)) :
    𝓢(Space d, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (bandCut d Λ) F

/-- The Fourier transform of the truncation is the cutoff multiple of `𝓕 F`. -/
theorem fourier_bandTrunc (d : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) (F : 𝓢(Space d, ℂ)) :
    𝓕 (bandTrunc d Λ hΛ F) = SchwartzMap.smulLeftCLM ℂ (bandCut d Λ) (𝓕 F) := by
  unfold bandTrunc
  rw [SchwartzMap.fourierMultiplierCLM_apply]
  exact FourierInvPair.fourier_fourierInv_eq _

/-- **The truncation is band-limited.**  Its Fourier transform vanishes at every
frequency of norm at least `2Λ`. -/
theorem fourier_bandTrunc_eq_zero (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (F : 𝓢(Space d, ℂ))
    {ξ : Space d} (hξ : 2 * Λ ≤ ‖ξ‖) :
    𝓕 (bandTrunc d Λ hΛ.ne' F) ξ = 0 := by
  rw [fourier_bandTrunc]
  rw [SchwartzMap.smulLeftCLM_apply (bandCut_temperate d Λ hΛ.ne')]
  change bandCut d Λ ξ • (𝓕 F) ξ = 0
  rw [bandCut_eq_zero d Λ hΛ hξ, zero_smul]

end LatticeProb.Sobolev
