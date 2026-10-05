/-
# The quantitative translation bound for the Fréchet–Kolmogorov route

`TranslationContinuity.lean` proved the Fourier translation identity
`𝓕 (fun x => φ (x + h)) = fun ξ => 𝐞 ⟪h, ξ⟫ • 𝓕 φ ξ`.  This module turns it
into the
**quantitative translation bound** whose `η`-form is `BandLimitedTranslationContinuous`
(`FrechetKolmogorov.lean`), the analytic half of the `H^s`-unit-ball translation-continuity.

The ingredients are:

* `fourier_sub_lift` — linearity of `𝓕` in the function (from `fourierIntegral_add`);
* `norm_fourierChar_sub_one_le` — the phase estimate `‖𝐞 t − 1‖ ≤ 4π|t|` for
  `2π|t| ≤ 1`;
* `fourier_translate_sub_lift` — the difference form of the translation identity.
-/
import LatticeProb.Analysis.Sobolev.TranslationContinuity

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **Linearity of `𝓕` in the function.**  `𝓕 (f - g) = 𝓕 f - 𝓕 g` for integrable
`f, g`. -/
theorem fourier_sub_lift {d : ℕ} {f g : Space d → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  have h := VectorFourier.fourierIntegral_add (μ := volume) (L := innerₗ (Space d))
    Real.continuous_fourierChar continuous_inner (hf.sub hg) hg
  rw [show (f - g) + g = f from sub_add_cancel f g] at h
  exact eq_sub_of_add_eq h.symm

/-- **The phase estimate.**  `‖𝐞 t − 1‖ ≤ 4π|t|` for `2π|t| ≤ 1`, from
`Complex.norm_exp_sub_one_le`.  This is the small-frequency bound that makes the phase factor of
the translation identity vanish as `h → 0`. -/
theorem norm_fourierChar_sub_one_le {t : ℝ} (ht : 2 * Real.pi * |t| ≤ 1) :
    ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ 4 * Real.pi * |t| := by
  rw [Real.fourierChar_apply', Circle.coe_exp]
  have hx : ‖(((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one,
      show ‖(((2 * Real.pi * t : ℝ)) : ℂ)‖ = |2 * Real.pi * t| from by simp,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact ht
  refine (Complex.norm_exp_sub_one_le hx).trans ?_
  rw [Complex.norm_mul, Complex.norm_I, mul_one,
    show ‖(((2 * Real.pi * t : ℝ)) : ℂ)‖ = |2 * Real.pi * t| from by simp,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  exact le_of_eq (by ring)

/-- **The difference form of the translation identity.**
`𝓕 (fun x => φ(x + h) − φ x) = fun ξ => (𝐞 ⟪h, ξ⟫ − 1) • 𝓕 φ ξ`, for an
integrable
`φ`. -/
theorem fourier_translate_sub_lift {d : ℕ} (φ : Space d → ℂ) (h : Space d)
    (hf : Integrable φ) (hf' : Integrable fun x => φ (x + h)) :
    𝓕 (fun x => φ (x + h) - φ x)
      = fun ξ => ((𝐞 (inner ℝ h ξ) : ℂ) - 1) • 𝓕 φ ξ := by
  change 𝓕 ((fun x => φ (x + h)) - φ)
    = fun ξ => ((𝐞 (inner ℝ h ξ) : ℂ) - (1 : ℂ)) • 𝓕 φ ξ
  rw [fourier_sub_lift hf' hf, fourier_comp_add_right_lift φ h]
  funext ξ
  change 𝐞 (inner ℝ h ξ) • 𝓕 φ ξ - 𝓕 φ ξ
    = ((𝐞 (inner ℝ h ξ) : ℂ) - 1) • 𝓕 φ ξ
  rw [Circle.smul_def, smul_eq_mul]
  ring

end LatticeProb.Sobolev
