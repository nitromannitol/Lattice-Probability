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
-/
import LatticeProb.External.GaussianLogSobolev
import LatticeProb.Prob.GaussianLogSobolevEntropy
import LatticeProb.Prob.GaussianLogSobolevMollify
import LatticeProb.Prob.GaussEuclideanPushforward

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace LatticeProb

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
  have hmeas : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) :=
    WithLp.measurable_ofLp (p := 2) (Fin n → ℝ)
  have hpush : ∀ F : (Fin n → ℝ) → ℝ, Continuous F →
      ∫ x, F (WithLp.ofLp x) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))
        = ∫ y, F y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    intro F hF
    rw [← GaussConc.gaussEuclid_map_ofLp n,
      integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
  have hhc : Continuous h := hc.continuous
  rw [hpush (fun y => h y * Real.log (h y))
      (hhc.mul (hhc.log fun x => (hpos x).ne')), hpush h hhc, hnorm] at key
  simpa using key

/-- **The Gaussian logarithmic Sobolev inequality holds in every dimension.** -/
theorem gaussianLogSobolev_holds (n : ℕ) : GaussianLogSobolev n := by
  intro h hpos hint hlog hnorm C hlip
  obtain ⟨hε, hprops, htend⟩ := lipschitzLogApprox n h C hpos hlip hint hlog hnorm
  refine le_of_tendsto' htend fun k => ?_
  obtain ⟨hp, hc, hlc, -, -, -, hnk⟩ := hprops k
  exact integral_mul_log_le_of_contDiff hp hc hlc hnk

end LatticeProb
