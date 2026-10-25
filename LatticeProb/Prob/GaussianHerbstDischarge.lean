module

public import LatticeProb.Prob.GaussLipConcentration
public import LatticeProb.Prob.GaussEuclideanPushforward
public import LatticeProb.Prob.GaussianHerbst
public import LatticeProb.External.GaussianLogSobolev
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# The Gaussian Herbst bound holds in every dimension

The cited Herbst exponential moment input `LatticeProb.GaussianHerbstBound n` of
`LatticeProb.Prob.GaussianHerbst` holds for every `n`, unconditionally. The proof transfers a
Lipschitz function on `Fin n → ℝ` with the sup metric to the Euclidean space
`EuclideanSpace ℝ (Fin n)`, where the standard Gaussian pushes forward to the product of
standard Gaussians. There the sharp sub-Gaussian MGF bound of the Gaussian concentration
inequality for Lipschitz functions (`LatticeProb.GaussConc.mgf_le_of_lipschitz`) applies with
the same constant.

The corollary `gaussian_lipschitz_concentration_unconditional` is the concentration inequality
of `LatticeProb.Prob.GaussianHerbst` with the Herbst hypothesis removed.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- The Gaussian Herbst bound holds in every dimension. -/
theorem gaussianHerbstBound_all (n : ℕ) : GaussianHerbstBound n := by
  intro f L hL hf lam _
  have hmeas : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) :=
    WithLp.measurable_ofLp (p := 2) (Fin n → ℝ)
  -- Pushing a continuous integrand along `ofLp` turns the Euclidean Gaussian into the product.
  have hpush : ∀ h : (Fin n → ℝ) → ℝ, Continuous h →
      ∫ x, h (WithLp.ofLp x) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))
        = ∫ y, h y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    intro h hh
    rw [← GaussConc.gaussEuclid_map_ofLp n,
      integral_map hmeas.aemeasurable hh.aestronglyMeasurable]
  -- The sup-metric Lipschitz constant `L` is also a Euclidean one, since `ofLp` is 1-Lipschitz.
  have hg : LipschitzWith ⟨L, hL.le⟩ (fun x : EuclideanSpace ℝ (Fin n) => f (WithLp.ofLp x)) := by
    have := hf.comp (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ))
    rwa [mul_one] at this
  have h := GaussConc.mgf_le_of_lipschitz hg lam
  have hc := hpush f hf.continuous
  have hcont : Continuous fun y => Real.exp (lam * (f y -
      ∫ z, f z ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1))) :=
    (continuous_const.mul (hf.continuous.sub continuous_const)).rexp
  calc ∫ x, Real.exp (lam * (f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = ∫ x, Real.exp (lam * (f (WithLp.ofLp x) -
          ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := (hpush _ hcont).symm
    _ = mgf (fun x => f (WithLp.ofLp x) -
          ∫ y, f (WithLp.ofLp y) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))))
          (stdGaussian (EuclideanSpace ℝ (Fin n))) lam := by
        rw [hc, mgf]
    _ ≤ Real.exp (lam ^ 2 * L ^ 2 / 2) := h

/-- **Gaussian concentration for a Lipschitz functional of `n` independent standard Gaussians,
unconditionally in the dimension**: `gaussian_lipschitz_concentration` with the Herbst hypothesis
discharged by `gaussianHerbstBound_all`. -/
theorem gaussian_lipschitz_concentration_unconditional (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : LipschitzWith ⟨L, hL.le⟩ f) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
        {x | t ≤ f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)}
      ≤ Real.exp (-(t ^ 2) / (2 * L ^ 2)) :=
  gaussian_lipschitz_concentration n (gaussianHerbstBound_all n) f L hL hf t ht

/-! ### Nonvacuity example -/

-- Nonvacuity: the coordinate `x ↦ x 0` on `Fin 2 → ℝ` is `1`-Lipschitz for the sup metric,
-- and its concentration inequality holds with no Herbst hypothesis.
example (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).real
        {x : Fin 2 → ℝ | t ≤ x 0 - ∫ y, y 0 ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1)}
      ≤ Real.exp (-(t ^ 2) / (2 * 1 ^ 2)) :=
  gaussian_lipschitz_concentration_unconditional 2 (fun x => x 0) 1 one_pos
    (LipschitzWith.of_dist_le_mul fun x y => (dist_le_pi_dist x y 0).trans_eq (one_mul _).symm)
    t ht

end LatticeProb
