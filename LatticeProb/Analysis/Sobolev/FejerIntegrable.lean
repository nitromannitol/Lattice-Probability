/-
# The Fejér side condition: `m · 𝓕 φ` and its transform are integrable

This finishes the second side condition of the smoothed Fejér route started in
`FejerSideCondition.lean`.  For Schwartz `m` and `φ`:

* `fourier_convolution_fourierInv_mul` — item 1: `𝓕 ((𝓕⁻ m) ⋆ φ) = m · 𝓕 φ`, the
  product is the Fourier transform of a genuine `L¹ ∩ L²` convolution;
* `integrable_convolution_fourierInv_mul` — item 2, Young: `(𝓕⁻ m) ⋆ φ` is integrable
  as the convolution of two `L¹` Schwartz functions;
* `integrable_fourier_mul_conv` — item 2, conclusion: `𝓕 (m · 𝓕 φ)` is integrable,
  read through item 1 and the double-inversion reflection `𝓕 (𝓕 h) = h ∘ (-·)`;
* `fejer_integrable_side_condition` — the side condition bundled for the Fejér
  route: `m · 𝓕 φ` and its Fourier transform are both integrable.

The Fejér limit `m → 1_{‖ξ‖ ≤ Λ}` and the boundary sphere stay out of scope.
-/
import LatticeProb.Analysis.Sobolev.FejerSideCondition
import LatticeProb.Analysis.Sobolev.FrequencyTruncation

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Convolution

namespace LatticeProb.Sobolev

/-- **Item 1.**  The Fourier transform of the convolution of `φ` with the Schwartz
kernel `𝓕⁻ m` is the product `m · 𝓕 φ`. -/
theorem fourier_convolution_fourierInv_mul (d : ℕ) (m φ : 𝓢(Space d, ℂ)) (ξ : Space d) :
    𝓕 ((𝓕⁻ m : 𝓢(Space d, ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ)) ξ
      = m ξ * 𝓕 φ ξ := by
  have h := SchwartzMap.fourier_convolution_apply (ContinuousLinearMap.mul ℂ ℂ)
    (𝓕⁻ m) φ ξ
  rw [← h, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    FourierTransform.fourier_fourierInv_eq]
  rfl

/-- **Item 2, Young.**  The convolution of two `L¹` Schwartz functions is integrable. -/
theorem integrable_convolution_fourierInv_mul (d : ℕ) (m φ : 𝓢(Space d, ℂ)) :
    Integrable ((𝓕⁻ m : 𝓢(Space d, ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ)) volume :=
  (𝓕⁻ m).integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) φ.integrable

/-- **Item 2, conclusion.**  The Fourier transform of `m · 𝓕 φ` is integrable, read
through item 1 and the double-inversion reflection. -/
theorem integrable_fourier_mul_conv (d : ℕ) (m φ : 𝓢(Space d, ℂ)) :
    Integrable (𝓕 (fun ξ => m ξ * 𝓕 φ ξ)) volume := by
  have hmem : Integrable ((𝓕⁻ m : 𝓢(Space d, ℂ))
      ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ)) volume :=
    integrable_convolution_fourierInv_mul d m φ
  have hpoint : (fun ξ => m ξ * 𝓕 φ ξ)
      = 𝓕 ((𝓕⁻ m : 𝓢(Space d, ℂ))
          ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ)) := by
    funext ξ
    exact (fourier_convolution_fourierInv_mul d m φ ξ).symm
  rw [hpoint]
  have hcont : Continuous ((𝓕⁻ m : 𝓢(Space d, ℂ))
      ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ)) := by
    rw [show ((𝓕⁻ m : 𝓢(Space d, ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ))
        = ⇑(SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ m) φ) from
      funext (fun x =>
        (SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ m) φ x).symm)]
    exact (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ m) φ).continuous
  have hF : Integrable (𝓕 ((𝓕⁻ m : 𝓢(Space d, ℂ))
      ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ))) := by
    have hEq : 𝓕 ((𝓕⁻ m : 𝓢(Space d, ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ))
        = ⇑(SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) m (𝓕 φ)) := by
      funext ξ
      rw [fourier_convolution_fourierInv_mul d m φ ξ, SchwartzMap.pairing_apply_apply]
      rfl
    rw [hEq]
    exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) m (𝓕 φ)).integrable
  have hdouble : 𝓕 (𝓕 ((𝓕⁻ m : 𝓢(Space d, ℂ))
      ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ)))
      = fun ξ => ((𝓕⁻ m : 𝓢(Space d, ℂ))
          ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ)) (-ξ) := by
    funext ξ
    calc 𝓕 (𝓕 ((𝓕⁻ m : 𝓢(Space d, ℂ))
          ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ))) ξ
        = 𝓕 (𝓕 ((𝓕⁻ m : 𝓢(Space d, ℂ))
            ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ))) (-(-ξ)) := by
          rw [neg_neg]
      _ = 𝓕⁻ (𝓕 ((𝓕⁻ m : 𝓢(Space d, ℂ))
            ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (φ : Space d → ℂ))) (-ξ) :=
          (Real.fourierInv_eq_fourier_neg _ (-ξ)).symm
      _ = _ := hmem.fourierInv_fourier_eq hF (hcont.continuousAt)
  rw [hdouble]
  exact hmem.comp_neg

/-- **The Fejér side condition, bundled.**  For a Schwartz cutoff `m` and a Schwartz
`φ`, the product `m · 𝓕 φ` and its Fourier transform are both integrable. -/
theorem fejer_integrable_side_condition (d : ℕ) (m φ : 𝓢(Space d, ℂ)) :
    Integrable (fun ξ => m ξ * 𝓕 φ ξ) volume ∧
      Integrable (𝓕 (fun ξ => m ξ * 𝓕 φ ξ)) volume := by
  refine ⟨?_, integrable_fourier_mul_conv d m φ⟩
  have h : (fun ξ => m ξ * 𝓕 φ ξ)
      = ⇑(SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) m (𝓕 φ)) := by
    funext ξ
    rw [SchwartzMap.pairing_apply_apply]
    rfl
  rw [h]
  exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) m (𝓕 φ)).integrable

end LatticeProb.Sobolev
