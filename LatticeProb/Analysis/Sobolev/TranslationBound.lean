/-
# The quantitative translation bound for the Fréchet–Kolmogorov route

`TranslationContinuity.lean` proved the Fourier translation identity
`𝓕 (fun x => φ (x + h)) = fun ξ => 𝐞 ⟪h, ξ⟫ • 𝓕 φ ξ`.  This module gives the
**quantitative translation bound** ingredients: linearity of `𝓕` in the function, the
difference form of the translation identity, and the phase estimate `‖𝐞 t − 1‖ ≤ 4π|t|`
for `2π|t| ≤ 1`.  These feed the uniform translation-continuity of the `H^s`-unit ball,
the analytic half of `BandLimitedTranslationContinuous` (`FrechetKolmogorov.lean`), the
input of the Fréchet–Kolmogorov route to the Rellich low-frequency compactness.
-/
import LatticeProb.Analysis.Sobolev.TranslationContinuity

open MeasureTheory Filter
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **Linearity of `𝓕`.**  `𝓕 (f - g) = 𝓕 f - 𝓕 g` for integrable `f, g`. -/
theorem fourier_sub_lift {d : ℕ} {f g : Space d → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  have hfg : Integrable (f - g) := hf.sub hg
  have h := VectorFourier.fourierIntegral_add (μ := volume) (L := innerₗ (Space d))
    Real.continuous_fourierChar continuous_inner hfg hg
  rw [show (f - g) + g = f from sub_add_cancel f g] at h
  exact eq_sub_of_add_eq h.symm

/-- **The phase estimate.**  `‖𝐞 t − 1‖ ≤ 4π|t|` for `2π|t| ≤ 1`, from
`Complex.norm_exp_sub_one_le`.  This is the small-frequency bound that makes the phase factor of
the translation identity vanish as `h → 0`. -/
theorem norm_fourierChar_sub_one_le {t : ℝ} (ht : 2 * Real.pi * |t| ≤ 1) :
    ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ 4 * Real.pi * |t| := by
  have hnorm : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => Complex.ofRealLI.norm_map r
  rw [Real.fourierChar_apply', Circle.coe_exp]
  have hx : ‖(((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one, hnorm, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact ht
  have h := Complex.norm_exp_sub_one_le hx
  rw [Complex.norm_mul, Complex.norm_I, mul_one, hnorm, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **The difference form of the translation identity.**  For a test function `φ`,
`𝓕 (φ(· + h) − φ) = fun ξ => (𝐞 ⟪h, ξ⟫ : ℂ) * 𝓕 φ ξ − 𝓕 φ ξ`. -/
theorem fourier_translate_sub_lift {d : ℕ} (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (h : Space d) :
    𝓕 (fun x => ((φ (x + h) - φ x : ℝ) : ℂ))
      = fun ξ => (((𝐞 (inner ℝ h ξ) : Circle)) : ℂ) * 𝓕 (fun x => (φ x : ℂ)) ξ
          - 𝓕 (fun x => (φ x : ℂ)) ξ := by
  have hg : Integrable (fun x : Space d => ((φ x : ℝ) : ℂ)) :=
    (hcont.continuous.integrable_of_hasCompactSupport hcs).ofReal
  have hf : Integrable (fun x : Space d => ((φ (x + h) : ℝ) : ℂ)) := hg.comp_add_right h
  have hshift : (fun x : Space d => ((φ (x + h) - φ x : ℝ) : ℂ))
      = (fun x : Space d => ((φ (x + h) : ℝ) : ℂ))
        - (fun x : Space d => ((φ x : ℝ) : ℂ)) := by
    funext x; simp [Complex.ofReal_sub]
  rw [hshift]
  rw [fourier_sub_lift hf hg, fourier_comp_add_right_lift (fun x => (φ x : ℂ)) h]
  ext ξ
  simp only [Pi.sub_apply, Circle.smul_def, smul_eq_mul]

end LatticeProb.Sobolev
