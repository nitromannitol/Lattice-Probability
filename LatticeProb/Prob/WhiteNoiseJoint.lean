/-
Jointly measurable versions of the canonical white noise along a spatial `L²` family.

The canonical white noise `LatticeProb.whiteNoiseOf μ` is a Gaussian family indexed by
square-integrable functions, and its covariance is the `L²` inner product.  When the index
moves with a parameter — a family `u ↦ f u` of test functions that is strongly measurable as
an `L²`-valued map — the evaluations `u ↦ whiteNoiseOf μ (f u) ω` have a version jointly
measurable in `(u, ω)`.  This is the measurability clause a stochastic Fubini needs when a
white-noise integral is interchanged with an integral over an independent parameter space.
-/
import LatticeProb.Gauss.WhiteNoise
import LatticeProb.Prob.L2JointVersion

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

/-- **Jointly measurable versions of the canonical white noise along a strongly
measurable spatial `L²` family.**  For a family `f : U → X → ℝ` of square-integrable test
functions whose `L²` classes depend strongly measurably on the parameter, there is a jointly
measurable `g` with `g u =ᵐ[whiteNoiseLaw μ] whiteNoiseOf μ (f u)` for every `u`. -/
theorem exists_joint_version_whiteNoiseOf {X U : Type*} [MeasurableSpace X]
    [MeasurableSpace U] (μ : Measure X) [IsSeparable μ]
    (f : U → X → ℝ) (hf : ∀ u, MemLp (f u) 2 μ)
    (hF : StronglyMeasurable (fun u => (hf u).toLp (f u))) :
    ∃ g : U → (↥(l2Basis μ) → ℝ) → ℝ,
      StronglyMeasurable (Function.uncurry g) ∧
      ∀ u, g u =ᵐ[whiteNoiseLaw μ] whiteNoiseOf μ (f u) := by
  exact exists_joint_version_of_covariance μ (whiteNoiseLaw μ) (whiteNoiseOf μ)
    (fun f => (isGaussianProcess_whiteNoiseOf μ).hasGaussianLaw_eval f |>.memLp_two)
    (fun f g hf hg => integral_whiteNoiseOf_mul μ hf hg) f hf hF

end LatticeProb
