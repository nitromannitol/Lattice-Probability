/-
# The weighted Young convolution inequality for the Sobolev norm

## Intended lemma list, in dependency order

1. `sobolevWeight` — the Sobolev weight of exponent `s` at the frequency `ξ`, namely
   `(1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s`.  This is the weight that the definition `sobolevNormSq`
   uses, written once so that the later statements can name it.
2. `sobolevWeight_nonneg` — the weight is nonnegative.
3. `sobolevNormSq_eq_lintegral_weight` — the definition `sobolevNormSq` written through
   `sobolevWeight`.
4. `norm_fourier_lift_convReal_le` — the pointwise Young bound: for integrable real functions `f`
   and `ρ` and every frequency `ξ`, the norm of the Fourier transform of the convolution
   `f ⋆ ρ` at `ξ` is at most the norm of the Fourier transform of `f` at `ξ` multiplied by the
   `L¹` norm `∫ y, |ρ y|` of `ρ`.  The proof factors the Fourier transform of the convolution
   through the library lemma `fourier_lift_convReal` and bounds the Fourier transform of `ρ` by its
   `L¹` norm through the Mathlib lemma
   `VectorFourier.norm_fourierIntegral_le_integral_norm`.
5. `sobolevNormSq_convReal_le` — the weighted Young convolution inequality: for integrable real
   functions `f` and `ρ`, the squared `H^s` norm of `convReal f ρ` is at most
   `(∫ y, |ρ y|) ^ 2` multiplied by the squared `H^s` norm of `f`.  The proof compares the
   integrands pointwise through `norm_fourier_lift_convReal_le`, integrates the comparison with
   `lintegral_mono`, and pulls the constant out with `lintegral_const_mul'`.

## Relation to the residual `SobolevMollificationEstimate`

The inequality `sobolevNormSq_convReal_le` is the bounding step of the standard proof of the
residual `SobolevMollificationEstimate` (`FrechetKolmogorovMollifyResidual.lean:38`).  The residual
itself needs, in addition, the averaging identity

`f - convReal f ρ = ∫ y, ρ y • (fun x => f (x + y) - f x)`

for a kernel `ρ` of total mass one, the corresponding `H^s` bound of that average by the
`L¹`-average
of the translation errors, and the choice of `ρ` inside the radius supplied by the
translation-continuity hypothesis.  Those steps are not in this file.
-/
import LatticeProb.Analysis.Sobolev.SobolevConvolution
import LatticeProb.Analysis.Sobolev.Additivity

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- The Sobolev weight of exponent `s` at the frequency `ξ`, namely
`(1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s`.  This is the weight used by `sobolevNormSq`. -/
noncomputable def sobolevWeight {d : ℕ} (s : ℝ) (ξ : Space d) : ℝ :=
  (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s

/-- The Sobolev weight is nonnegative. -/
theorem sobolevWeight_nonneg {d : ℕ} (s : ℝ) (ξ : Space d) : 0 ≤ sobolevWeight s ξ := by
  unfold sobolevWeight
  exact Real.rpow_nonneg (by positivity) s

/-- The definition `sobolevNormSq` written through the named weight `sobolevWeight`. -/
theorem sobolevNormSq_eq_lintegral_weight {d : ℕ} (s : ℝ) (φ : Space d → ℝ) :
    sobolevNormSq d s φ
      = ∫⁻ ξ : Space d, ENNReal.ofReal
          (sobolevWeight s ξ * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
  unfold sobolevNormSq sobolevWeight
  rfl

/-- **The pointwise Young bound for the convolution.**  For integrable real functions `f` and `ρ`
and every frequency `ξ`, the norm of the Fourier transform of `convReal f ρ` at `ξ` is at
most the norm of the Fourier transform of `f` at `ξ` multiplied by the `L¹` norm
`∫ y, |ρ y|` of `ρ`. -/
theorem norm_fourier_lift_convReal_le {d : ℕ} {f ρ : Space d → ℝ}
    (hf : Integrable f) (hρ : Integrable ρ) (ξ : Space d) :
    ‖𝓕 (fun x => (convReal f ρ x : ℂ)) ξ‖
      ≤ ‖𝓕 (fun x => (f x : ℂ)) ξ‖ * ∫ y, |ρ y| := by
  have hfactor := congrFun (fourier_lift_convReal hf hρ) ξ
  rw [hfactor, Pi.mul_apply, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hbound : ‖𝓕 (fun x => (ρ x : ℂ)) ξ‖
      ≤ ∫ y : Space d, ‖((ρ y : ℝ) : ℂ)‖ := by
    change ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (Space d))
        (fun x => (ρ x : ℂ)) ξ‖ ≤ _
    exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ (Space d)) (fun x => (ρ x : ℂ)) ξ
  refine hbound.trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ‖((ρ y : ℝ) : ℂ)‖ = |ρ y|
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- **The weighted Young convolution inequality for the Sobolev norm.**  For every real exponent
`s` and every pair of integrable real functions `f` and `ρ` on `Space d`, the squared `H^s` norm of
the convolution `convReal f ρ` is at most the square of the `L¹` norm `∫ y, |ρ y|` of `ρ`
multiplied
by the squared `H^s` norm of `f`. -/
theorem sobolevNormSq_convReal_le {d : ℕ} (s : ℝ) {f ρ : Space d → ℝ}
    (hf : Integrable f) (hρ : Integrable ρ) :
    sobolevNormSq d s (convReal f ρ)
      ≤ ENNReal.ofReal ((∫ y, |ρ y|) ^ 2) * sobolevNormSq d s f := by
  set c : ℝ := ∫ y, |ρ y| with hcdef
  have hc0 : 0 ≤ c := integral_nonneg fun y => abs_nonneg _
  rw [sobolevNormSq_eq_lintegral_weight s (convReal f ρ),
    sobolevNormSq_eq_lintegral_weight s f]
  have hpoint : ∀ ξ : Space d,
      ENNReal.ofReal (sobolevWeight s ξ * ‖𝓕 (fun x => (convReal f ρ x : ℂ)) ξ‖ ^ 2)
        ≤ ENNReal.ofReal (c ^ 2)
          * ENNReal.ofReal (sobolevWeight s ξ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    have hw := sobolevWeight_nonneg s ξ
    have hb := norm_fourier_lift_convReal_le hf hρ ξ
    have hb2 : ‖𝓕 (fun x => (convReal f ρ x : ℂ)) ξ‖ ^ 2
        ≤ ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 * c ^ 2 := by
      nlinarith [hb, norm_nonneg (𝓕 (fun x => (convReal f ρ x : ℂ)) ξ),
        norm_nonneg (𝓕 (fun x => (f x : ℂ)) ξ), hc0]
    have hprod : sobolevWeight s ξ * ‖𝓕 (fun x => (convReal f ρ x : ℂ)) ξ‖ ^ 2
        ≤ sobolevWeight s ξ * (‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 * c ^ 2) :=
      mul_le_mul_of_nonneg_left hb2 hw
    refine (ENNReal.ofReal_le_ofReal hprod).trans (le_of_eq ?_)
    rw [show sobolevWeight s ξ * (‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 * c ^ 2)
          = c ^ 2 * (sobolevWeight s ξ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) by ring,
      ENNReal.ofReal_mul (sq_nonneg c)]
  calc ∫⁻ ξ : Space d, ENNReal.ofReal
        (sobolevWeight s ξ * ‖𝓕 (fun x => (convReal f ρ x : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ : Space d, ENNReal.ofReal (c ^ 2)
          * ENNReal.ofReal (sobolevWeight s ξ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) :=
        lintegral_mono hpoint
    _ = ENNReal.ofReal (c ^ 2) * ∫⁻ ξ : Space d, ENNReal.ofReal
          (sobolevWeight s ξ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end LatticeProb.Sobolev
