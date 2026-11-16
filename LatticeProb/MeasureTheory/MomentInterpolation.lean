import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Interpolation of nonnegative moments -/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A moment between the first and the `q`th is bounded by the weighted
geometric mean of those moments. The measure need not be finite. -/
theorem lintegral_rpow_le_first_mul_rpow_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : Ω → ℝ≥0∞} (hF : AEMeasurable F μ)
    {q θ : ℝ} (hq : 0 ≤ q) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∫⁻ ω, F ω ^ (θ + (1 - θ) * q) ∂μ ≤
      (∫⁻ ω, F ω ∂μ) ^ θ * (∫⁻ ω, F ω ^ q ∂μ) ^ (1 - θ) := by
  have h1 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hh := ENNReal.lintegral_mul_norm_pow_le hF (hF.pow_const q) hθ h1
    (show θ + (1 - θ) = 1 by ring)
  have heq (ω : Ω) : F ω ^ (θ + (1 - θ) * q) =
      F ω ^ θ * (F ω ^ q) ^ (1 - θ) := by
    rw [ENNReal.rpow_add_of_nonneg _ _ hθ (mul_nonneg h1 hq)]
    congr 1
    rw [mul_comm (1 - θ) q, ENNReal.rpow_mul]
  simpa only [heq] using hh

/-- Geometric first-moment bounds and uniform `q`th-moment bounds interpolate
at every index. -/
theorem lintegral_rpow_le_of_geometric_first_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : ℕ → Ω → ℝ≥0∞} {A B ρ : ℝ≥0∞} {q θ : ℝ}
    (hq : 0 ≤ q) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hfirst : ∀ n, ∫⁻ ω, F n ω ∂μ ≤ A * ρ ^ n)
    (hqbound : ∀ n, ∫⁻ ω, F n ω ^ q ∂μ ≤ B) (n : ℕ) :
    ∫⁻ ω, F n ω ^ (θ + (1 - θ) * q) ∂μ ≤
      (A * ρ ^ n) ^ θ * B ^ (1 - θ) := by
  exact (lintegral_rpow_le_first_mul_rpow_moment (hF n) hq hθ hθ1).trans
    (mul_le_mul' (ENNReal.rpow_le_rpow (hfirst n) hθ)
      (ENNReal.rpow_le_rpow (hqbound n) (sub_nonneg.mpr hθ1)))

end LatticeProb
