/-
# The real test-function truncation and its Fourier characteristic identity

This bridges the real test functions of the Rellich–Kondrachov framework to the
smooth complex truncation `bandTrunc` of `FrequencyTruncation.lean`.

* `realToComplexSchwartz` packages a real `C^∞` compactly supported function as a
  complex Schwartz map, and `fourier_realToComplexSchwartz` identifies its Fourier
  transform with the pointwise transform of the coerced function.
* `fourier_bandTrunc_real` is the characteristic identity of the smooth
  truncation on the complexified test function: the Fourier transform of
  `bandTrunc (φc)` is `bandCut · 𝓕 φ`, and `fourier_bandTrunc_real_eq_zero` reads
  off that this transform vanishes beyond `2Λ`.
* `bandProj` is the real part of the complex truncation, the real-valued
  candidate for the low-frequency approximation.

The remaining step for the real-valued characteristic identity,
`𝓕 (fun x => (bandProj … x : ℂ)) = bandCut · 𝓕 (fun x => (φ x : ℂ))`, is the
realness of `bandTrunc (φc)`: see the docstring of `bandProj`.  It needs the
Fourier transform of a real part / of a conjugation, which Mathlib does not
provide; the sharp-indicator identity is not stated here.
-/
import LatticeProb.Analysis.Sobolev.FrequencyTruncation
import LatticeProb.Analysis.Sobolev.BandLimited

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace LatticeProb.Sobolev

/-- The complexification of a real smooth compactly supported function, as a
complex Schwartz map. -/
noncomputable def realToComplexSchwartz (d : ℕ) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) : 𝓢(Space d, ℂ) :=
  (hcs.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hcont)

/-- The complex Schwartz map is the pointwise coercion of the real function. -/
@[simp] theorem realToComplexSchwartz_coe (d : ℕ) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (x : Space d) :
    realToComplexSchwartz d φ hcont hcs x = (φ x : ℂ) := rfl

/-- The Fourier transform of the complexified function is the pointwise Fourier
transform of the coerced function. -/
theorem fourier_realToComplexSchwartz (d : ℕ) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (ξ : Space d) :
    𝓕 (realToComplexSchwartz d φ hcont hcs) ξ = 𝓕 (fun x => (φ x : ℂ)) ξ := by
  have h := congrFun (SchwartzMap.fourier_coe (realToComplexSchwartz d φ hcont hcs)) ξ
  rw [h]
  rfl

/-- **The characteristic identity of the truncation, on the complexified test
function.**  The Fourier transform of the smooth truncation of `φc` is the cutoff
multiple of `𝓕 φ`. -/
theorem fourier_bandTrunc_real (d : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) (ξ : Space d) :
    𝓕 (bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs)) ξ
      = (bandCut d Λ ξ : ℂ) * 𝓕 (fun x => (φ x : ℂ)) ξ := by
  rw [fourier_bandTrunc]
  rw [SchwartzMap.smulLeftCLM_apply_apply (bandCut_temperate d Λ hΛ)]
  rw [fourier_realToComplexSchwartz]
  rfl

/-- The truncation of a complexified test function has vanishing Fourier
transform beyond `2Λ`. -/
theorem fourier_bandTrunc_real_eq_zero (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    {ξ : Space d} (hξ : 2 * Λ ≤ ‖ξ‖) :
    𝓕 (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs)) ξ = 0 :=
  fourier_bandTrunc_eq_zero d Λ hΛ _ hξ

/-- **The real truncation.**  The real part of the complex smooth truncation: the
real-valued candidate for the low-frequency approximation of a test function.

Its characteristic identity `𝓕 (fun x => (bandProj … x : ℂ)) ξ = bandCut d Λ ξ *
𝓕 (fun x => (φ x : ℂ)) ξ` is exactly the realness of `bandTrunc (φc)`, i.e.
`∀ x, (bandTrunc d Λ hΛ (φc) x).im = 0`.  That realness is the missing input: it
is equivalent, through the inversion theorem, to the conjugate-symmetry of
`bandCut · 𝓕 φc` (`𝓕 φc` is conjugate-symmetric because `φc` is real-valued and
`bandCut` is real and even), and Mathlib has no Fourier transform of a real part
or of a complex conjugate to run that argument.  `fourier_bandTrunc_real` is the
same identity one level up, for the complex function `bandTrunc (φc)` itself. -/
noncomputable def bandProj (d : ℕ) (Λ : ℝ) (hΛ : Λ ≠ 0) (φ : Space d → ℝ)
    (hcont : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) : Space d → ℝ :=
  fun x => (bandTrunc d Λ hΛ (realToComplexSchwartz d φ hcont hcs) x).re

end LatticeProb.Sobolev
