/-
The canonical white noise as a continuous linear map on `L²`.

`LatticeProb.whiteNoiseOf μ` is the isonormal process of the Hilbert basis of `L²(μ)`,
so it is the composition of the isometry `gaussIso` with the basis representation; as a
map on `Lp ℝ 2 μ` it is continuous and linear.  This is the form in which the noise is
integrated against a random test function: the pairing `∫ ω, W f ω ∂P` is the `L²`
integral of the image of `f`, and the map is what carries measurability of `f ↦ W f`.

The pointwise identity with `whiteNoiseOf` is definitional.
-/
import LatticeProb.Gauss.WhiteNoise

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsSeparable μ]

/-- The canonical white noise as a continuous linear map on `L²(μ)`. -/
noncomputable def whiteNoiseCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (whiteNoiseLaw μ) :=
  (gaussIso (ι := ↥(l2Basis μ))).toContinuousLinearMap.comp
    (l2HilbertBasis μ).repr.toLinearIsometry.toContinuousLinearMap

theorem coeFn_whiteNoiseCLM_toLpOrZero (f : X → ℝ) :
    (fun ω => whiteNoiseCLM μ (toLpOrZero μ f) ω) =ᵐ[whiteNoiseLaw μ] whiteNoiseOf μ f := by rfl


end LatticeProb
