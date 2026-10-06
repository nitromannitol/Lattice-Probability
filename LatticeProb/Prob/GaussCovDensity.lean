/-
# The density of the centred Gaussian `N(0, S)` as a function on `Fin n → ℝ`

Li--Shao normal comparison, route items 3 and 4
(`scratch/pk/normalcompare-route.md`).  `LatticeProb.multivariateGaussian_eq_withDensity`
(`LatticeProb/Gauss/MultivariateDensity.lean`) gives the density of `N(0, S)` on
`EuclideanSpace ℝ (Fin n)` for a positive definite `S`.  The differentiation steps of the route
(coordinate partials, the covariance derivative) are cleanest on plain functions
`Fin n → ℝ`, where `Function.update` is available, so this file names that density once:

  `covDensity S x = (2π)^{-n/2} (det S)^{-1/2} exp (-(x ⬝ᵥ S⁻¹ *ᵥ x)/2)`,

proves it positive, and restates `multivariateGaussian_eq_withDensity` in terms of it.
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonDensity

open MeasureTheory ProbabilityTheory Matrix

namespace LatticeProb

/-- The density of the centred Gaussian `N(0, S)` as a function on `Fin n → ℝ`:
`(2π)^{-n/2} (det S)^{-1/2} exp (-(x ⬝ᵥ S⁻¹ *ᵥ x)/2)`. -/
noncomputable def covDensity {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) * (S.det) ^ (-(1 : ℝ) / 2) *
    Real.exp (-(x ⬝ᵥ (S⁻¹ *ᵥ x)) / 2)

/-- The density of a positive definite Gaussian is strictly positive. -/
theorem covDensity_pos {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (x : Fin n → ℝ) : 0 < covDensity S x := by
  unfold covDensity
  have h2pi : 0 < 2 * Real.pi := by positivity [Real.pi_pos]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos h2pi _) (Real.rpow_pos_of_pos hS.det_pos _))
    (Real.exp_pos _)

/-- `LatticeProb.multivariateGaussian_eq_withDensity` in terms of `covDensity`. -/
theorem multivariateGaussian_eq_withDensity_covDensity {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
      = (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (fun y => ENNReal.ofReal (covDensity S (WithLp.ofLp y))) :=
  multivariateGaussian_eq_withDensity S hS

end LatticeProb
