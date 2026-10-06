/-
Convolution and its Fourier transform for real and complex functions.
-/
import LatticeProb.Analysis.Sobolev.Defs

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- Convolution of two real functions. -/
noncomputable def convReal {d : ℕ} (f ρ : Space d → ℝ) : Space d → ℝ :=
  convolution f ρ (ContinuousLinearMap.mul ℝ ℝ) volume

/-- The Fourier transform of an integrable complex convolution is the product of
the Fourier transforms. -/
theorem fourier_convolution_lift {d : ℕ} (u v : Space d → ℂ) (hu : Integrable u)
    (hv : Integrable v) :
    𝓕 (convolution u v (ContinuousLinearMap.mul ℂ ℂ) volume) = 𝓕 u * 𝓕 v :=
  funext fun ξ => Real.fourier_mul_convolution_eq hu hv ξ

/-- The complex lift of a real convolution is the convolution of the complex lifts. -/
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

/-- The Fourier transform of the complex lift of a real convolution factors for
integrable inputs. -/
theorem fourier_lift_convReal {d : ℕ} {f ρ : Space d → ℝ} (hf : Integrable f)
    (hρ : Integrable ρ) :
    𝓕 (fun x => (convReal f ρ x : ℂ))
      = 𝓕 (fun x => (f x : ℂ)) * 𝓕 (fun x => (ρ x : ℂ)) := by
  rw [lift_convReal]
  exact fourier_convolution_lift (fun x => (f x : ℂ)) (fun x => (ρ x : ℂ))
    hf.ofReal hρ.ofReal

end LatticeProb.Sobolev
