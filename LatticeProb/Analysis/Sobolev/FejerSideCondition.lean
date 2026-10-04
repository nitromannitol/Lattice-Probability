/-
# The Fejér side condition: the product `m · 𝓕 φ` is a Fourier transform

The smoothed (Fejér) route to the Rellich–Kondrachov band identity replaces the
sharp indicator `1_{‖ξ‖ ≤ Λ}` by a Schwartz multiplier `m`.  Its second side
condition — the reason the smoothing helps — is that the product `m · 𝓕 φ` is the
Fourier transform of a genuine function, so that the Fourier inversion and the
integrability tests apply.  This module packages that fact from Mathlib's
Schwartz convolution rule `SchwartzMap.fourier_convolution`:

* `mul_fourier_eq_fourier_convolution` — the product `m · 𝓕 φ` is the Fourier
  transform of the convolution of `φ` with the Schwartz kernel `𝓕⁻ m`
  (`fourier_convolution` with `f = 𝓕⁻ m`, `g = φ`, so no reflection is needed);
* `integrable_fourier_mul` — the Fourier transform of `m · 𝓕 φ` is integrable
  (it is Schwartz), the second side condition;
* `fourier_smul` — the band identity `𝓕 (P_m φ) = m · 𝓕 φ` at the function level
  for the Fourier multiplier `P_m := fourierMultiplierCLM m`, the Schwartz
  analogue of `fourier_bandTrunc`.

The limiting step `m → 1_{‖ξ‖ ≤ Λ}` (monotone/dominated convergence of
`sobolevNormSqHigh` along a Fejér sequence) is not attempted here: it is the
boundary-sphere point recorded in `fejer-band-step.md`.
-/
import LatticeProb.Analysis.Sobolev.FrequencyTruncation

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace LatticeProb.Sobolev

/-- **The convolution identity.**  The product of a Schwartz multiplier and the
Fourier transform of a Schwartz function is the Fourier transform of the
convolution of `φ` with the Schwartz kernel `𝓕⁻ m`. -/
theorem mul_fourier_eq_fourier_convolution (d : ℕ) (m φ : 𝓢(Space d, ℂ))
    (ξ : Space d) :
    m ξ * 𝓕 φ ξ
      = 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ m) φ) ξ := by
  rw [SchwartzMap.fourier_convolution]
  rw [SchwartzMap.pairing_apply_apply, FourierTransform.fourier_fourierInv_eq]
  rfl

/-- **The second side condition.**  The Fourier transform of the product
`m · 𝓕 φ` is integrable for Schwartz `m` and `φ`. -/
theorem integrable_fourier_mul (d : ℕ) (m φ : 𝓢(Space d, ℂ)) :
    Integrable (𝓕 (fun ξ => m ξ * 𝓕 φ ξ)) volume := by
  have h : (fun ξ => m ξ * 𝓕 φ ξ)
      = ⇑(SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) m (𝓕 φ)) := by
    ext ξ
    rw [SchwartzMap.pairing_apply_apply]
    rfl
  rw [h, ← SchwartzMap.fourier_coe]
  exact (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) m (𝓕 φ))).integrable

/-- **The band identity for a Schwartz multiplier.**  The Fourier transform of
the Fourier multiplier by `m` is the pointwise product `m · 𝓕 φ`. -/
theorem fourier_smul (d : ℕ) (m φ : 𝓢(Space d, ℂ)) :
    𝓕 (SchwartzMap.fourierMultiplierCLM ℂ (⇑m) φ)
      = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) m (𝓕 φ) := by
  rw [SchwartzMap.fourierMultiplierCLM_apply]
  have h : SchwartzMap.smulLeftCLM ℂ (⇑m) (𝓕 φ)
      = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) m (𝓕 φ) := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply m.hasTemperateGrowth]
    rw [SchwartzMap.pairing_apply_apply]
    rfl
  rw [h]
  exact FourierInvPair.fourier_fourierInv_eq _

end LatticeProb.Sobolev
