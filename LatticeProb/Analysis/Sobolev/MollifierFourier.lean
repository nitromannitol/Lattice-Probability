/-
# The Fourier transform of a dilation and the mollifier normalisation

The density input of the Rellich support repair (`MollifierFourierTendsto`, consumed by
`exists_testFn_approx_of_fourier_tendsto` in `SupportDensity.lean`) needs the standard
**scaling identity** for the Fourier transform of a rescaled function,

  `𝓕 (fun x => f (a • x)) w = (a ^ d)⁻¹ • 𝓕 f (a⁻¹ • w)`  (`a > 0`),

whose `a → ∞` corollary `𝓕 f (· / a) → 𝓕 f 0 = ∫ f` is the pointwise
convergence of the
mollifier Fourier transforms.  Mathlib has the two ingredients but not the identity:
`MeasureTheory.Measure.integral_comp_smul_of_nonneg`
(`MeasureTheory/Measure/Haar/NormedSpace.lean`) does the substitution, and `Real.fourier_eq`
with `VectorFourier.fourierIntegral_continuous` gives the pointwise form and the continuity of
`𝓕 f`.  This file lands the identity, its companions, and the whole normalised-dilation
mollifier: `mollifierFourierTendsto` proves `MollifierFourierTendsto`, i.e.
`𝓕 χ_n → 1` pointwise and `‖𝓕 χ_n‖ ≤ 1` for `χ_n x = n^d • φ (n • x)`
with `∫ φ = 1`.
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory Filter
open scoped FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The Fourier transform of a dilation.**  For `a > 0` and `f : Space d → ℂ`,
`𝓕 (fun x => f (a • x)) w = (a ^ d)⁻¹ • 𝓕 f (a⁻¹ • w)`.  This is the
scaling identity the
mollifier argument needs; it is not in Mathlib. -/
theorem fourier_comp_smul {d : ℕ} (f : Space d → ℂ) {a : ℝ} (ha : 0 < a)
    (w : Space d) :
    𝓕 (fun x => f (a • x)) w = (a ^ d)⁻¹ • 𝓕 f (a⁻¹ • w) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hinner : ∀ v : Space d, inner ℝ (a • v) (a⁻¹ • w) = inner ℝ v w := by
    intro v
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ ha.ne',
      one_mul]
  have hsc := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ := volume)
    (fun v : Space d => 𝐞 (-(inner ℝ v (a⁻¹ • w))) • f v) a (hR := ha.le)
  have hL : (∫ v, 𝐞 (-(inner ℝ (a • v) (a⁻¹ • w))) • f (a • v))
      = ∫ v, 𝐞 (-(inner ℝ v w)) • f (a • v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    change 𝐞 (-(inner ℝ (a • v) (a⁻¹ • w))) • f (a • v)
      = 𝐞 (-(inner ℝ v w)) • f (a • v)
    rw [hinner v]
  rw [hL] at hsc
  rw [finrank_euclideanSpace, Fintype.card_fin] at hsc
  exact hsc

/-- **The Fourier transform at frequency zero is the integral.**  `𝓕 f 0 = ∫ f`. -/
theorem fourier_zero_eq_integral {d : ℕ} (f : Space d → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  rw [Real.fourier_eq]
  simp

/-- **The Fourier transform is continuous** for an integrable function. -/
theorem continuous_fourier {d : ℕ} {f : Space d → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ (Space d))
    Real.continuous_fourierChar continuous_inner hf

/-- **The constant-scalar rule for the Fourier transform.**  `𝓕 (c • f) = c • 𝓕 f`. -/
theorem fourier_const_smul {d : ℕ} (c : ℂ) (f : Space d → ℂ) :
    𝓕 (c • f) = c • 𝓕 f :=
  VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ (Space d)) f c

/-- **The normalised dilation has no scaling factor.**  For `χ_a x = a^d • f (a • x)`,
`𝓕 (χ_a) w = 𝓕 f (a⁻¹ • w)`: the `a^d` normalisation cancels the `(a^d)⁻¹` of
`fourier_comp_smul`. -/
theorem fourier_normalized_dilation {d : ℕ} (f : Space d → ℂ) {a : ℝ} (ha : 0 < a)
    (w : Space d) :
    𝓕 (fun x => ((a ^ d : ℝ) : ℂ) • f (a • x)) w = 𝓕 f (a⁻¹ • w) := by
  have hconst : 𝓕 (fun x => ((a ^ d : ℝ) : ℂ) • f (a • x)) w
      = ((a ^ d : ℝ) : ℂ) • 𝓕 (fun x => f (a • x)) w :=
    congrFun (fourier_const_smul ((a ^ d : ℝ) : ℂ) (fun x => f (a • x))) w
  rw [hconst, fourier_comp_smul f ha w]
  have hpow : (a ^ d : ℝ) ≠ 0 := pow_ne_zero d ha.ne'
  rw [smul_eq_mul, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hpow, Complex.ofReal_one, one_mul]

/-- The normalised dilations of `φ`: `χ n x = (n + 1)^d • φ ((n + 1) • x)`.
Shifting the index by
one keeps the scale `n + 1` strictly positive, so no `0`-scale case arises. -/
noncomputable def mollifierDil (d : ℕ) (φ : Space d → ℂ) (n : ℕ) : Space d → ℂ :=
  fun x => ((((n : ℝ) + 1) ^ d : ℝ) : ℂ) • φ (((n : ℝ) + 1) • x)

/-- The Fourier transform of the normalised dilation is the Fourier transform of `φ` at the
rescaled frequency. -/
theorem fourier_mollifierDil {d : ℕ} (φ : Space d → ℂ) (n : ℕ) (ξ : Space d) :
    𝓕 (mollifierDil d φ n) ξ = 𝓕 φ (((n : ℝ) + 1)⁻¹ • ξ) :=
  fourier_normalized_dilation φ (by positivity) ξ

/-- The uniform bound `‖𝓕 χ_n‖ ≤ 1` for a normalised `φ`. -/
theorem norm_fourier_mollifierDil_le {d : ℕ} {φ : Space d → ℂ}
    (hnorm : ∫ x, ‖φ x‖ ≤ 1) (n : ℕ) (ξ : Space d) :
    ‖𝓕 (mollifierDil d φ n) ξ‖ ≤ 1 := by
  rw [fourier_mollifierDil φ n ξ]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ (Space d)) φ (((n : ℝ) + 1)⁻¹ • ξ)).trans hnorm

/-- **The mollifier Fourier transforms tend to `1`.**  For `φ` with `∫ φ = 1`,
`𝓕 χ_n ξ → 1` at every frequency. -/
theorem tendsto_fourier_mollifierDil {d : ℕ} {φ : Space d → ℂ} (hf : Integrable φ)
    (hint : ∫ x, φ x = 1) (ξ : Space d) :
    Tendsto (fun n : ℕ => 𝓕 (mollifierDil d φ n) ξ) atTop (𝓝 1) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • ξ) atTop (𝓝 0) := by
    simpa using h1.smul_const ξ
  have h3 : Tendsto (fun n : ℕ => 𝓕 φ (((n : ℝ) + 1)⁻¹ • ξ)) atTop
      (𝓝 (𝓕 φ 0)) :=
    ((continuous_fourier hf).tendsto 0).comp h2
  rw [fourier_zero_eq_integral, hint] at h3
  exact Tendsto.congr'
    (Filter.Eventually.of_forall fun n => (fourier_mollifierDil φ n ξ).symm) h3

/-- **The mollifier Fourier-normalisation data.**  For a normalised bump `φ` (`∫ φ = 1`,
`∫ ‖φ‖ ≤ 1`), the normalised dilations `χ_n` satisfy `𝓕 χ_n → 1` pointwise and
`‖𝓕 χ_n‖ ≤ 1`.
This is the input `exists_testFn_approx_of_fourier_tendsto` (`SupportDensity.lean`) consumes. -/
def MollifierFourierTendsto (d : ℕ) (φ : Space d → ℂ) : Prop :=
  (∀ ξ : Space d, Tendsto (fun n : ℕ => 𝓕 (mollifierDil d φ n) ξ) atTop (𝓝 1)) ∧
  (∀ (n : ℕ) (ξ : Space d), ‖𝓕 (mollifierDil d φ n) ξ‖ ≤ 1)

/-- `MollifierFourierTendsto` holds for every normalised bump. -/
theorem mollifierFourierTendsto {d : ℕ} {φ : Space d → ℂ} (hf : Integrable φ)
    (hint : ∫ x, φ x = 1) (hnorm : ∫ x, ‖φ x‖ ≤ 1) :
    MollifierFourierTendsto d φ :=
  ⟨fun ξ => tendsto_fourier_mollifierDil hf hint ξ,
    fun n ξ => norm_fourier_mollifierDil_le hnorm n ξ⟩

end LatticeProb.Sobolev
