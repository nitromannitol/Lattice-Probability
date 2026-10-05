/-
# The convolution Fourier factor for the real lift

`SupportDensity.fourier_convolution_lift` is the `ℂ`-valued convolution theorem for the Fourier
notation.  The two classical halves of the Fréchet–Kolmogorov reduction
(`FrechetKolmogorovMollify`, `FrechetKolmogorovMollifiedCompact`) both need its **real** form,

  `𝓕 (lift (f ⋆ ρ)) = 𝓕 (lift f) · 𝓕 (lift ρ)`,

which follows once `lift (f ⋆_ℝ ρ) = lift f ⋆_ℂ lift ρ`.
-/
import LatticeProb.Analysis.Sobolev.SupportDensity
import LatticeProb.Analysis.Sobolev.FrechetKolmogorovReduce

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **The lift of the real convolution.**  For `f, ρ : Space d → ℝ`,
`lift (f ⋆_ℝ ρ) = lift f ⋆_ℂ lift ρ` (no integrability needed:
`integral_ofReal` is unconditional). -/
theorem lift_convReal {d : ℕ} {f ρ : Space d → ℝ} :
    (fun x => (convReal f ρ x : ℂ))
      = convolution (fun x => (f x : ℂ)) (fun x => (ρ x : ℂ))
          (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  simp only [convReal, convolution_def]
  rw [show (↑(∫ t, (ContinuousLinearMap.mul ℝ ℝ) (f t) (ρ (x - t)) ∂volume) : ℂ)
        = ∫ t, ↑((ContinuousLinearMap.mul ℝ ℝ) (f t) (ρ (x - t))) ∂volume
      from (integral_ofReal (μ := volume) (𝕜 := ℂ)
        (f := fun t : Space d => (ContinuousLinearMap.mul ℝ ℝ) (f t)
          (ρ (x - t)))).symm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (↑(f t * ρ (x - t)) : ℂ) = (f t : ℂ) * (ρ (x - t) : ℂ)
  exact Complex.ofReal_mul _ _

/-- **The convolution Fourier factor for the real lift.**
`𝓕 (lift (f ⋆ ρ)) = 𝓕 (lift f) · 𝓕 (lift ρ)` for integrable `f, ρ`. -/
theorem fourier_lift_convReal {d : ℕ} {f ρ : Space d → ℝ} (hf : Integrable f)
    (hρ : Integrable ρ) :
    𝓕 (fun x => (convReal f ρ x : ℂ))
      = 𝓕 (fun x => (f x : ℂ)) * 𝓕 (fun x => (ρ x : ℂ)) := by
  rw [lift_convReal]
  exact fourier_convolution_lift (fun x => (f x : ℂ)) (fun x => (ρ x : ℂ))
    hf.ofReal hρ.ofReal

end LatticeProb.Sobolev
