/-
# The Fourier transform of a dilation (the missing scaling identity)

The density input of the Rellich support repair (`MollifierFourierTendsto`, consumed by
`exists_testFn_approx_of_fourier_tendsto` in `SupportDensity.lean`) needs the standard
**scaling identity** for the Fourier transform of a rescaled function,

  `𝓕 (fun x => f (a • x)) w
    = (a ^ d)⁻¹ • 𝓕 f (a⁻¹ • w)`  (`a > 0`),

whose `a → ∞` corollary `𝓕 f (· / a) → 𝓕 f 0 = ∫ f` is the pointwise
convergence of the
mollifier Fourier transforms.  Mathlib has the two ingredients but not the identity:
`MeasureTheory.Measure.integral_comp_smul_of_nonneg`
(`MeasureTheory/Measure/Haar/NormedSpace.lean`) does the substitution, and `Real.fourier_eq`
with `VectorFourier.fourierIntegral_continuous` gives the pointwise form and the continuity of
`𝓕 f`.  This file lands the identity and its companions.
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory
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

end LatticeProb.Sobolev
