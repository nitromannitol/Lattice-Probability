/-
# The Gaussian logarithmic Sobolev inequality, proved

The proposition `LatticeProb.GaussianLogSobolev n` (Gross 1975, in the Herbst form: a positive
probability density `h` of the standard Gaussian product law on `Fin n → ℝ` whose logarithm is
`C`-Lipschitz has entropy at most `C² / 2`) holds for every `n`, by `gaussianLogSobolev_holds`.

For a `C¹` density the statement is the exponential-tilt inequality
`LatticeProb.GaussLSI.integral_mul_log_le_of_gradient`, transported from
`EuclideanSpace ℝ (Fin n)` along `WithLp.ofLp`, which carries the standard Gaussian measure to the
product of standard Gaussians (`LatticeProb.GaussConc.gaussEuclid_map_ofLp`) and is `1`-Lipschitz
from the Euclidean to the sup metric (`integral_mul_log_le_of_contDiff`). A merely Lipschitz
logarithm is reached through the `C¹` approximations of `LatticeProb.lipschitzLogApprox`, which keep
the Lipschitz constant and the mass and converge in entropy.

The `ℓ²` form `LatticeProb.GaussianLogSobolevL2 n`, for logarithms that are `C`-Lipschitz for the
Euclidean distance, holds for every `n` as well (`gaussianLogSobolevL2_holds`), from the Lipschitz
exponential-tilt inequality `LatticeProb.GaussLSI.integral_exp_mul_le_of_lipschitz`.
-/
import LatticeProb.External.GaussianLogSobolev
import LatticeProb.Prob.GaussianLogSobolevLipschitz
import LatticeProb.Prob.HerbstFromLSI
import LatticeProb.Prob.GaussianLogSobolevMollify
import LatticeProb.Prob.GaussEuclideanPushforward
import LatticeProb.Prob.GaussianLogSobolevTensor

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace LatticeProb

/-- Integrals of continuous functions transfer from `EuclideanSpace ℝ (Fin n)` with its standard
Gaussian measure to `Fin n → ℝ` with the product of standard Gaussians. -/
theorem integral_comp_ofLp_stdGaussian {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Continuous F) :
    ∫ x, F (WithLp.ofLp x) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))
      = ∫ y, F y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  rw [← GaussConc.gaussEuclid_map_ofLp n, integral_map
    (WithLp.measurable_ofLp (p := 2) (Fin n → ℝ)).aemeasurable hF.aestronglyMeasurable]

/-- **The Gaussian logarithmic Sobolev inequality for `C¹` densities** on `Fin n → ℝ` whose
logarithm is `C`-Lipschitz for the sup metric. -/
theorem integral_mul_log_le_of_contDiff {n : ℕ} {h : (Fin n → ℝ) → ℝ} (hpos : ∀ x, 0 < h x)
    (hc : ContDiff ℝ 1 h) {C : ℝ≥0} (hlip : LipschitzWith C fun x => Real.log (h x))
    (hnorm : ∫ x, h x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 1) :
    ∫ x, h x * Real.log (h x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ≤ (C : ℝ) ^ 2 / 2 := by
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.log (h (WithLp.ofLp x)) with hgdef
  have hofLp : LipschitzWith 1 (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) :=
    PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ)
  have hg : LipschitzWith C g := by
    have h1 := hlip.comp hofLp
    rw [mul_one] at h1
    exact h1
  have hgc : ContDiff ℝ 1 g :=
    (hc.log fun x => (hpos x).ne').comp (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ))
  have hgd : ∀ x, HasGradientAt g (gradient g x) x := fun x =>
    ((hgc.differentiable one_ne_zero) x).hasGradientAt
  have hg'c : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hgc.continuous_fderiv one_ne_zero)
  have hg'b : ∀ x, ‖gradient g x‖ ≤ C := fun x => by
    rw [gradient, LinearIsometryEquiv.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hg
  have key := GaussLSI.integral_mul_log_le_of_gradient hg hgd hg'c hg'b
  have hexp : ∀ x, Real.exp (g x) = h (WithLp.ofLp x) := fun x => Real.exp_log (hpos _)
  simp only [hexp] at key
  have hhc : Continuous h := hc.continuous
  rw [integral_comp_ofLp_stdGaussian (F := fun y => h y * Real.log (h y))
      (hhc.mul (hhc.log fun x => (hpos x).ne')), integral_comp_ofLp_stdGaussian hhc,
    hnorm] at key
  simpa using key

/-- **The Gaussian logarithmic Sobolev inequality holds in every dimension.** -/
theorem gaussianLogSobolev_holds (n : ℕ) : GaussianLogSobolev n := by
  intro h hpos hint hlog hnorm C hlip
  obtain ⟨hε, hprops, htend⟩ := lipschitzLogApprox n h C hpos hlip hint hlog hnorm
  refine le_of_tendsto' htend fun k => ?_
  obtain ⟨hp, hc, hlc, -, -, -, hnk⟩ := hprops k
  exact integral_mul_log_le_of_contDiff hp hc hlc hnk

/-- **The `ℓ²` form of the Gaussian logarithmic Sobolev inequality holds in every dimension.** -/
theorem gaussianLogSobolevL2_holds (n : ℕ) : GaussianLogSobolevL2 n := by
  intro h hpos _ _ hnorm C hlip
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.log (h (WithLp.ofLp x))
  have hg : LipschitzWith C g := LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, EuclideanSpace.dist_eq]
    refine (hlip (WithLp.ofLp x) (WithLp.ofLp y)).trans (le_of_eq ?_)
    simp [Real.dist_eq, sq_abs]
  have hh : h = fun y => Real.exp (g (WithLp.toLp 2 y)) :=
    funext fun y => (Real.exp_log (hpos y)).symm
  have hhc : Continuous h := by
    rw [hh]
    exact (hg.continuous.comp (by fun_prop)).rexp
  have key := GaussLSI.integral_exp_mul_le_of_lipschitz hg
  have hexp : ∀ x, Real.exp (g x) = h (WithLp.ofLp x) := fun x => Real.exp_log (hpos _)
  simp only [hexp] at key
  rw [integral_comp_ofLp_stdGaussian (F := fun y => h y * Real.log (h y))
      (hhc.mul (hhc.log fun x => (hpos x).ne')), integral_comp_ofLp_stdGaussian hhc,
    hnorm] at key
  simpa using key

/-- The one-dimensional Gaussian logarithmic Sobolev inequality `GaussianLogSobolevOne`. -/
theorem gaussianLogSobolevOne_holds : GaussianLogSobolevOne :=
  gaussianLogSobolev_holds 1

/-- The tensorization step `GaussianLogSobolevTensorStep` holds, since its conclusion
`GaussianLogSobolev (n + 1)` holds in every dimension. -/
theorem gaussianLogSobolevTensorStep_holds : GaussianLogSobolevTensorStep :=
  fun n _ => gaussianLogSobolev_holds (n + 1)

end LatticeProb
