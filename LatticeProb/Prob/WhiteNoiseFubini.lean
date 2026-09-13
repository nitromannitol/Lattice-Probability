/-
The stochastic Fubini identity for white noise.

A bounded linear map commutes with a Bochner integral.  Since white-noise evaluation is a
linear isometry of `L²(μ)` into `L²(P)`, the noise of a Bochner-averaged test function is
the average of the noises: `𝒲(∫ k dP_B) = ∫ 𝒲(k) dP_B` in `L²(P)`.  This is the
interchange a stochastic Fubini needs when a white-noise integral is taken against a
random test function.
-/
import LatticeProb.Prob.WhiteNoiseIsometry
import LatticeProb.Gauss.WhiteNoise

set_option linter.unusedVariables false

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {X Ω ΩB : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace ΩB]

/-- The noise of a Bochner-averaged test function is the average of the noises. -/
theorem whiteNoise_integral_comm (μ : Measure X) (P : Measure Ω)
    (W : (X → ℝ) → Ω → ℝ) (hm : ∀ f, MemLp (W f) 2 P)
    (hc : ∀ f g, MemLp f 2 μ → MemLp g 2 μ →
      (∫ ω, W f ω * W g ω ∂P) = ∫ x, f x * g x ∂μ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (k : ΩB → Lp ℝ 2 μ) (hk : Integrable k PB) :
    (whiteNoiseLinearIsometry μ P W hm hc (∫ ω', k ω' ∂PB))
      = ∫ ω', (whiteNoiseLinearIsometry μ P W hm hc (k ω')) ∂PB := (ContinuousLinearMap.integral_comp_comm (whiteNoiseLinearIsometry μ P W hm hc).toContinuousLinearMap hk).symm


/-- **The stochastic Fubini identity for the canonical white noise of a measure.**  The
noise of a Bochner-averaged test function is the average of the noises, for the canonical
white noise `whiteNoiseOf μ` on the `L²` basis of `μ`. -/
theorem whiteNoiseOf_integral_comm {X ΩB : Type*} [MeasurableSpace X] [MeasurableSpace ΩB]
    (μ : Measure X) [IsSeparable μ]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (k : ΩB → Lp ℝ 2 μ) (hk : Integrable k PB) :
    (whiteNoiseLinearIsometry μ (whiteNoiseLaw μ) (whiteNoiseOf μ)
        (fun f => (isGaussianProcess_whiteNoiseOf μ).hasGaussianLaw_eval f |>.memLp_two)
        (fun f g hf hg => integral_whiteNoiseOf_mul μ hf hg)) (∫ ω', k ω' ∂PB)
      = ∫ ω', (whiteNoiseLinearIsometry μ (whiteNoiseLaw μ) (whiteNoiseOf μ)
        (fun f => (isGaussianProcess_whiteNoiseOf μ).hasGaussianLaw_eval f |>.memLp_two)
        (fun f g hf hg => integral_whiteNoiseOf_mul μ hf hg)) (k ω') ∂PB :=
  whiteNoise_integral_comm μ (whiteNoiseLaw μ) (whiteNoiseOf μ)
    (fun f => (isGaussianProcess_whiteNoiseOf μ).hasGaussianLaw_eval f |>.memLp_two)
    (fun f g hf hg => integral_whiteNoiseOf_mul μ hf hg) PB k hk

end LatticeProb
