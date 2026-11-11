/-
# The `H^s`-structure packaging: `sobolevNormSq` as the Bessel-potential norm

Mathlib's `Analysis/Distribution/Sobolev.lean` has the Bessel potential
`besselPotential (s) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  `fourierMultiplierCLM F (fun x => (1 + ‖x‖²)^{s/2})`,
the Fourier-multiplier form
`fourier_besselPotential_eq_smulLeftCLM_fourier_apply`, and the membership
`MemSobolev (s p) f := ∃ f' : Lp F p volume, besselPotential s f = f'`.

This module names the packaging step that turns the project's `sobolevNormSq` (a `lintegral` of
`(1 + (2π‖ξ‖)²)^s · ‖𝓕(lift f) ξ‖²`) into the square of an `eLpNorm` — i.e. the `H^s` "norm" — so
that the `H^s`-valued Bochner integral (and hence the Minkowski average of the mollification
identity) becomes available.  The right-hand side is the Bessel-potential norm written directly on
the Fourier side (the `2π` normalisation is absorbed into `(2π‖ξ‖)²`).
-/
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- **The `H^s`-realisation bridge (named).**  The project's `sobolevNormSq d s f` is the square of
the `eLpNorm` (Bessel-potential `H^s` norm) of the weighted Fourier transform
`ξ ↦ ofReal((1 + (2π‖ξ‖)²)^{s/2}) · ofReal ‖𝓕(lift f) ξ‖`.  Provable from
`besselPotential`/`fourier_besselPotential_eq_smulLeftCLM_fourier_apply`
(`Analysis/Distribution/Sobolev.lean`)
together with the `lintegral`/`eLpNorm` bookkeeping; it is the input that realises
the kernel average
as an `H^s`-valued Bochner integral. -/
def SobolevNormBesselBridge : Prop :=
  ∀ (d : ℕ) (s : ℝ) (f : Space d → ℝ),
    sobolevNormSq d s f
      = (eLpNorm (fun ξ : Space d =>
            ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s / 2)) *
              ENNReal.ofReal ‖𝓕 (fun x => (f x : ℂ)) ξ‖) 2 volume) ^ 2

/-- **The weight-square form of `sobolevNormSq`.** -/
theorem sobolevNormSq_eq_lintegral_weight_sq {d : ℕ} (s : ℝ) (f : Space d → ℝ) :
    sobolevNormSq d s f
      = ∫⁻ ξ : Space d, (ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s / 2)) *
            ENNReal.ofReal ‖𝓕 (fun x => (f x : ℂ)) ξ‖) ^ 2 := by
  unfold sobolevNormSq
  refine lintegral_congr fun ξ => ?_
  have hW : ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s / 2)) *
        ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s / 2))
      = (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + (2 * Real.pi * ‖ξ‖) ^ 2)]
    congr 1
    ring
  conv_rhs => rw [pow_two, mul_mul_mul_comm]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s / 2)),
    ← ENNReal.ofReal_mul (norm_nonneg (𝓕 (fun x => (f x : ℂ)) ξ)),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤
      ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s / 2)) * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s / 2))),
    hW]
  congr 1
  ring

/-- **The `eLpNorm` square conversion.**  For `ℝ≥0∞`-valued `g`,
`(eLpNorm g 2 μ)² = ∫⁻ ξ, ‖g ξ‖ₑ ^ 2`; with `‖g ξ‖ₑ = g ξ` this is the `H^s`-norm realisation. -/
theorem sq_eLpNorm_two_eq_lintegral {d : ℕ} (g : Space d → ℝ≥0∞)
    (hg : AEStronglyMeasurable g volume) :
    (eLpNorm g 2 volume) ^ 2 = ∫⁻ ξ, (‖g ξ‖ₑ) ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := volume) (p := 2) (by norm_num) (by norm_num) hg]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]

/-- The Fourier transform `𝓕 (f : ℝ → ℂ)` of a real function is Borel measurable on `Space d`.
If `f` is integrable, `𝓕 f` is continuous (`VectorFourier.fourierIntegral_continuous`, the
Riemann-Lebesgue regime); otherwise the integrand `ξ`-by-`ξ` is not integrable
(`VectorFourier.fourierIntegral_convergent_iff`), so `𝓕 f` vanishes identically (Bochner
convention `integral_undef`). -/
theorem measurable_fourier_ofReal {d : ℕ} (f : Space d → ℝ) :
    Measurable (fun ξ : Space d => 𝓕 (fun x => (f x : ℂ)) ξ) := by
  by_cases hf : Integrable (fun x => (f x : ℂ)) volume
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).measurable
  · have h0 : (fun ξ : Space d => 𝓕 (fun x => (f x : ℂ)) ξ) = fun _ => 0 := by
      funext ξ
      refine integral_undef fun h => hf ?_
      exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ ξ).1 h
    rw [h0]
    exact measurable_const

/-- **The `H^s`-realisation bridge (proved).**  `SobolevNormBesselBridge` holds: combining
`sobolevNormSq_eq_lintegral_weight_sq` with `sq_eLpNorm_two_eq_lintegral`. -/
theorem sobolevNormBesselBridge : SobolevNormBesselBridge := by
  intro d s f
  rw [sobolevNormSq_eq_lintegral_weight_sq s f]
  have hmeas : Measurable (fun ξ : Space d =>
      ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s / 2)) *
        ENNReal.ofReal ‖𝓕 (fun x => (f x : ℂ)) ξ‖) :=
    (Measurable.ennreal_ofReal (by fun_prop)).mul
      (measurable_fourier_ofReal f).norm.ennreal_ofReal
  rw [sq_eLpNorm_two_eq_lintegral _ hmeas.aestronglyMeasurable]
  refine lintegral_congr fun ξ => ?_
  rw [enorm_eq_self]
  exact (ENNReal.rpow_natCast _ 2).symm

/-- **The `eLpNorm 1` Minkowski (integral triangle) form.**  For a two-variable `g`,
`eLpNorm (fun ξ => ∫ t, g t ξ) 1 μ ≤ ∫⁻ ξ, ∫⁻ t, ‖g t ξ‖ₑ ∂ν ∂μ`, i.e. the Bochner-integral triangle
inequality `enorm_integral_le_lintegral_enorm` transported to the `eLpNorm 1` seminorm
(`eLpNorm_one_eq_lintegral_enorm`).  This is the Minkowski step of the `H^s`-valued averaging. -/
theorem eLpNorm_one_integral_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (g : β → α → G) (ν : Measure β) (μ : Measure α)
    (hmeas : AEStronglyMeasurable (fun ξ => ∫ t, g t ξ ∂ν) μ) :
    eLpNorm (fun ξ => ∫ t, g t ξ ∂ν) 1 μ ≤ ∫⁻ ξ, ∫⁻ t, ‖g t ξ‖ₑ ∂ν ∂μ := by
  rw [eLpNorm_one_eq_lintegral_enorm hmeas]
  refine lintegral_mono fun ξ => ?_
  exact enorm_integral_le_lintegral_enorm (fun t => g t ξ)

end LatticeProb.Sobolev
