/-
# The falsity of the unrestricted low-frequency support repair: the analytic core

`LatticeProb.Sobolev.BandLimitedTestFnApprox` (`RellichLowFreqGlue.lean`) ranges over *every*
compactly supported `φ` while demanding a *fixed* net of test functions on the bounded domain `D`.
It is false: a bump translated to infinity is not covered, because the projection of the translate
keeps a fixed `H^{s₀}` size while its oscillatory pairing with any fixed `D`-supported test
function tends to `0`.

This module lands the three analytic facts the refutation rests on.

* `sobolevNormSq_comp_sub`: the Fourier-side Sobolev norm is translation-invariant, because a
  translation multiplies the Fourier transform by a phase of modulus one.
* `sobolevNormSq_zero_eq_integral_sq`: at `s = 0` the norm is the `L²` norm, through Plancherel and
  the `∫⁻`/`ofReal` bookkeeping (`ofReal_integral_eq_lintegral_ofReal`).
* `ofReal_integral_sq_sub_lower`: the weighted `∫⁻ ofReal (p ‖α − β‖²)` is at least the weighted
  `p‖α‖²` integral minus the absolute value of the oscillatory pairing `∫ 2 p Re (α conj β)`.
  This is the algebraic lower bound that keeps the oscillation, so that the bound does not
  degrade with the size of the test function `β`.

The remaining assembly is the fixed-data construction (`d = 1`, `D` a bounded domain, a fixed
bump, the normalisation, and the choice of the accuracy below the fixed level), the identification
of the Fourier transform of a translated projection through `fourier_bandProj` and
`fourier_comp_add_right_lift`, the positivity of the fixed level, and the Riemann–Lebesgue limit
`tendsto_integral_exp_inner_smul_cocompact` of the oscillatory pairing.  The pointwise-at-zero
route is *not* enough: a test function on `D` may carry an arbitrarily large `L¹` norm and so can
match the projection locally; it is the global oscillation of the translate that defeats the net.
-/
import LatticeProb.Analysis.Sobolev.FejerLimit
import LatticeProb.Analysis.Sobolev.Scaling
import LatticeProb.Analysis.Sobolev.TranslationContinuity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology SchwartzMap

namespace LatticeProb.Sobolev

/-- **Translation invariance of the Fourier-side Sobolev norm.** -/
theorem sobolevNormSq_comp_sub (d : ℕ) (s : ℝ) (φ : Space d → ℝ) (R : Space d) :
    sobolevNormSq d s (fun x => φ (x - R)) = sobolevNormSq d s φ := by
  unfold sobolevNormSq
  refine lintegral_congr fun ξ => ?_
  have h : ‖𝓕 (fun x : Space d => ((φ (x - R) : ℝ) : ℂ)) ξ‖
      = ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ := by
    have hfun : (fun x : Space d => ((φ (x - R) : ℝ) : ℂ))
        = (fun x : Space d => (fun y : Space d => ((φ y : ℝ) : ℂ)) (x + (-R))) := by
      funext x; rw [sub_eq_add_neg]
    rw [hfun, fourier_comp_add_right_lift (fun y : Space d => ((φ y : ℝ) : ℂ)) (-R)]
    simp
  rw [h]

/-- **Plancherel in the form consumed by `sobolevNormSq` at `s = 0`.** -/
theorem sobolevNormSq_zero_eq_integral_sq {d : ℕ} (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    sobolevNormSq d 0 φ = ENNReal.ofReal (∫ x, (φ x) ^ 2) := by
  set g : 𝓢(Space d, ℂ) := realToComplexSchwartz d φ hcont hcs with hg
  have hpt : ∀ ξ : Space d, 𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ = (𝓕 g) ξ := by
    intro ξ
    rw [hg]
    exact (fourier_realToComplexSchwartz d φ hcont hcs ξ).symm
  have hInt : Integrable (fun ξ : Space d => ‖(𝓕 g) ξ‖ ^ 2) :=
    (𝓕 g).memLp 2 |>.integrable_norm_pow (by norm_num)
  have hnn : 0 ≤ᵐ[volume] fun ξ : Space d => ‖(𝓕 g) ξ‖ ^ 2 :=
    ae_of_all _ fun ξ => sq_nonneg _
  rw [sobolevNormSq]
  have h0 : ∀ ξ : Space d, (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (0 : ℝ) = 1 := by
    intro ξ; rw [Real.rpow_zero]
  simp_rw [h0, one_mul, hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  congr 1
  rw [SchwartzMap.integral_norm_sq_fourier]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hg, realToComplexSchwartz_coe, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The pointwise complex identity `‖a - b‖² = ‖a‖² + ‖b‖² - 2 (a * conj b).re`. -/
private theorem norm_sq_sub_complex (a b : ℂ) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * starRingEnd ℂ b).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]

/-- **The lower bound.** -/
theorem ofReal_integral_sq_sub_lower {d : ℕ} {p : Space d → ℝ} {α β : Space d → ℂ}
    (hp0 : ∀ ξ, 0 ≤ p ξ)
    (hab : Integrable (fun ξ => p ξ * ‖α ξ - β ξ‖ ^ 2))
    (ha : Integrable (fun ξ => p ξ * ‖α ξ‖ ^ 2))
    (hb : Integrable (fun ξ => p ξ * ‖β ξ‖ ^ 2))
    (hx : Integrable (fun ξ => 2 * p ξ * (α ξ * starRingEnd ℂ (β ξ)).re)) :
    ENNReal.ofReal (∫ ξ, p ξ * ‖α ξ‖ ^ 2)
        - ENNReal.ofReal |∫ ξ, 2 * p ξ * (α ξ * starRingEnd ℂ (β ξ)).re|
      ≤ ∫⁻ ξ, ENNReal.ofReal (p ξ * ‖α ξ - β ξ‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hab
    (ae_of_all _ fun ξ => mul_nonneg (hp0 ξ) (sq_nonneg _))]
  rw [← ENNReal.ofReal_sub (∫ ξ, p ξ * ‖α ξ‖ ^ 2) (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hsplit : ∫ ξ, p ξ * ‖α ξ - β ξ‖ ^ 2
      = (∫ ξ, p ξ * ‖α ξ‖ ^ 2) + (∫ ξ, p ξ * ‖β ξ‖ ^ 2)
        - ∫ ξ, 2 * p ξ * (α ξ * starRingEnd ℂ (β ξ)).re := by
    calc ∫ ξ, p ξ * ‖α ξ - β ξ‖ ^ 2
        = ∫ ξ, (p ξ * ‖α ξ‖ ^ 2 + p ξ * ‖β ξ‖ ^ 2
            - 2 * p ξ * (α ξ * starRingEnd ℂ (β ξ)).re) := by
          apply integral_congr_ae
          filter_upwards with ξ
          rw [norm_sq_sub_complex]
          ring
      _ = (∫ ξ, (p ξ * ‖α ξ‖ ^ 2 + p ξ * ‖β ξ‖ ^ 2))
            - ∫ ξ, 2 * p ξ * (α ξ * starRingEnd ℂ (β ξ)).re :=
          integral_sub (ha.add hb) hx
      _ = ((∫ ξ, p ξ * ‖α ξ‖ ^ 2) + (∫ ξ, p ξ * ‖β ξ‖ ^ 2))
            - ∫ ξ, 2 * p ξ * (α ξ * starRingEnd ℂ (β ξ)).re := by
          rw [integral_add ha hb]
  have hD : 0 ≤ ∫ ξ, p ξ * ‖β ξ‖ ^ 2 :=
    integral_nonneg (μ := volume) fun ξ => mul_nonneg (hp0 ξ) (sq_nonneg _)
  have hkey : (∫ ξ, p ξ * ‖α ξ‖ ^ 2)
      ≤ (∫ ξ, p ξ * ‖α ξ - β ξ‖ ^ 2)
        + |∫ ξ, 2 * p ξ * (α ξ * starRingEnd ℂ (β ξ)).re| := by
    rw [hsplit]
    linarith [hD, le_abs_self (∫ ξ, 2 * p ξ * (α ξ * starRingEnd ℂ (β ξ)).re)]
  linarith [hkey]

end LatticeProb.Sobolev
