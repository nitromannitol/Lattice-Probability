/-
# The Fejér limit: the smooth truncation is genuinely band-limited

`BandTruncReal.lean` left open the *real-valued* characteristic identity of the
smooth truncation `bandProj`, i.e. the realness of `bandTrunc (φc)` for a real
test function `φ`.  This module closes it.

The key is the Fourier transform of a complex conjugation,

* `fourier_conj_comp`: `𝓕 (conj ∘ f) ξ = conj (𝓕 f (-ξ))`,

which Mathlib does not provide.  From it,
* `fourier_conj_symm`: a real-valued `f` has the conjugate-symmetric transform
  `𝓕 f (-ξ) = conj (𝓕 f ξ)`, and
* `fourierInv_conj_symm`: the inverse transform of a conjugate-symmetric
  function is real.

The multiplier `bandCut` is real and even (`bandCut_neg`), so
`bandCut · 𝓕 φc` is conjugate-symmetric and `bandTrunc (φc)` is real
(`bandTrunc_im_eq_zero`).  Consequently

* `fourier_bandProj`: `𝓕 (fun x => (bandProj … x : ℂ)) ξ = bandCut ξ · 𝓕 φ ξ`,
* `isBandLimited_bandProj`: `bandProj` is `2Λ`-band-limited,
* `sobolevNormSqHigh_bandProj_eq_zero`: its high-frequency part at `2Λ` vanishes.

The sharp boundary `‖ξ‖ = Λ` of the *cutoff* never enters: `bandCut` already
vanishes on the closed complement `‖ξ‖ ≥ 2Λ`, and `fourier_bandTrunc_eq_zero`
gives the vanishing pointwise, so no null-set argument is needed.  The
remaining Fejér limiting statement (dominated convergence of
`sobolevNormSqHigh` along a sequence of cutoffs shrinking onto `‖ξ‖ ≤ Λ`)
is not stated here; it needs finiteness of the weighted integral
`∫⁻ w_s ‖𝓕 φ‖²`, which Mathlib-level smoothness does supply but which is not
yet recorded for `sobolevNormSq`.
-/
import LatticeProb.Analysis.Sobolev.FejerIntegrable
import LatticeProb.Analysis.Sobolev.Weight
import LatticeProb.Analysis.Sobolev.BandTruncReal

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace LatticeProb.Sobolev

/-- The Fourier transform of a complex conjugation: conjugating the input
conjugates the transform and reflects the frequency. -/
private theorem fourier_conj_comp {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (f : V → ℂ) (ξ : V) :
    𝓕 (fun x => (starRingEnd ℂ) (f x)) ξ = (starRingEnd ℂ) (𝓕 f (-ξ)) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with v
  simp only [Circle.smul_def, smul_eq_mul]
  rw [map_mul]
  congr 1
  rw [← Circle.coe_inv_eq_conj]
  have hcirc : (𝐞 (-inner ℝ v (-ξ)))⁻¹ = 𝐞 (-inner ℝ v ξ) := by
    rw [← AddChar.map_neg_eq_inv 𝐞 (-inner ℝ v (-ξ)), neg_neg, inner_neg_right]
  rw [hcirc]

/-- A real-valued function has a conjugate-symmetric Fourier transform. -/
private theorem fourier_conj_symm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (f : V → ℂ) (hf : ∀ x, (starRingEnd ℂ) (f x) = f x) (ξ : V) :
    𝓕 f (-ξ) = (starRingEnd ℂ) (𝓕 f ξ) := by
  have hfun : (fun x => (starRingEnd ℂ) (f x)) = f := funext hf
  have h := fourier_conj_comp f (-ξ)
  rw [hfun, neg_neg] at h
  exact h

/-- The inverse Fourier transform of a conjugate-symmetric function is real. -/
private theorem fourierInv_conj_symm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {H : V → ℂ} (hH : ∀ ξ, (starRingEnd ℂ) (H ξ) = H (-ξ)) (x : V) :
    (starRingEnd ℂ) (𝓕⁻ H x) = 𝓕⁻ H x := by
  have h1 : (starRingEnd ℂ) (𝓕⁻ H x)
      = 𝓕 (fun ξ => (starRingEnd ℂ) (H ξ)) x := by
    rw [Real.fourierInv_eq_fourier_neg]
    exact (fourier_conj_comp H x).symm
  have h2 : (fun ξ => (starRingEnd ℂ) (H ξ)) = fun ξ => H (-ξ) := funext hH
  rw [h2] at h1
  rw [h1, ← Real.fourierInv_eq_fourier_comp_neg]

/-- The radial cutoff is even. -/
theorem bandCut_neg (d : ℕ) (Λ : ℝ) (ξ : Space d) :
    bandCut d Λ (-ξ) = bandCut d Λ ξ := by
  unfold bandCut
  rw [smul_neg, ContDiffBump.neg]

/-- **The truncation of a real function is real.**  If a complex Schwartz map is
pointwise real-valued, its smooth band truncation is too.  This is the realness
input that `bandProj` needs: `bandCut` is real and even, so `bandCut · 𝓕 F` is
conjugate-symmetric, and the inverse transform of a conjugate-symmetric
function is real. -/
theorem bandTrunc_im_eq_zero (d : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) (F : 𝓢(Space d, ℂ))
    (hF : ∀ x, (F x).im = 0) (x : Space d) :
    ((bandTrunc d Λ hΛ F) x).im = 0 := by
  set H := (SchwartzMap.smulLeftCLM ℂ (bandCut d Λ)) (𝓕 F) with hHdef

  have hsym : ∀ ξ, (𝓕 F) (-ξ) = (starRingEnd ℂ) ((𝓕 F) ξ) := by
    intro ξ
    rw [SchwartzMap.fourier_coe]
    exact fourier_conj_symm (⇑F) (fun y => (Complex.conj_eq_iff_im).2 (hF y)) ξ
  have hH : ∀ ξ, (starRingEnd ℂ) (H ξ) = H (-ξ) := by
    intro ξ
    rw [hHdef, SchwartzMap.smulLeftCLM_apply_apply (bandCut_temperate d Λ hΛ),
      SchwartzMap.smulLeftCLM_apply_apply (bandCut_temperate d Λ hΛ),
      bandCut_neg, hsym ξ]
    rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
  have hb : bandTrunc d Λ hΛ F = 𝓕⁻ H := by
    rw [bandTrunc, SchwartzMap.fourierMultiplierCLM_apply, ← hHdef]
  have hval : (bandTrunc d Λ hΛ F) x = 𝓕⁻ (H : Space d → ℂ) x := by
    rw [hb, SchwartzMap.fourierInv_coe]
  rw [hval]
  exact (Complex.conj_eq_iff_im).1 (fourierInv_conj_symm hH x)

/-- **The real-valued characteristic identity of the truncation.**  The Fourier
transform of the real projection `bandProj φ` is the cutoff multiple of `𝓕 φ`.
This is the identity `BandTruncReal.lean` left open. -/
theorem fourier_bandProj (d : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (ξ : Space d) :
    𝓕 (fun x => (bandProj d Λ hΛ φ hcont hcs x : ℂ)) ξ
      = (bandCut d Λ ξ : ℂ) * 𝓕 (fun x => (φ x : ℂ)) ξ := by
  have hcoe : (fun x => (bandProj d Λ hΛ φ hcont hcs x : ℂ))
      = ⇑(bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) := by
    funext x
    apply Complex.ext
    · change (((bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) x).re : ℂ).re
        = ((bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) x).re
      exact Complex.ofReal_re _
    · change (((bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) x).re : ℂ).im
        = ((bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) x).im
      rw [Complex.ofReal_im]
      exact (bandTrunc_im_eq_zero d Λ hΛ _ (fun y => by simp) x).symm
  rw [hcoe]
  have h := fourier_bandTrunc_real d Λ hΛ φ hcont hcs ξ
  rw [SchwartzMap.fourier_coe] at h
  exact h

/-- **The smooth projection is band-limited.**  `bandProj` has Fourier transform
supported in the closed ball of radius `2Λ`. -/
theorem isBandLimited_bandProj (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    IsBandLimited (2 * Λ) (bandProj d Λ hΛ.ne' φ hcont hcs) := by
  filter_upwards with ξ hξ
  rw [fourier_bandProj]
  rw [show bandCut d Λ ξ = 0 from bandCut_eq_zero d Λ hΛ (le_of_lt hξ)]
  simp

/-- **Item 2 of the Fejér packet.**  The high-frequency part of the smooth
projection vanishes at the band radius `2Λ`, the identity the truncation step of
the Rellich argument consumes. -/
theorem sobolevNormSqHigh_bandProj_eq_zero (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ)
    (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (s : ℝ) :
    sobolevNormSqHigh d s (2 * Λ) (bandProj d Λ hΛ.ne' φ hcont hcs) = 0 :=
  sobolevNormSqHigh_eq_zero_of_isBandLimited (s := s)
    (isBandLimited_bandProj d Λ hΛ φ hcont hcs)

end LatticeProb.Sobolev
