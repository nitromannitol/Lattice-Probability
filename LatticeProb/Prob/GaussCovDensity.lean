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
import LatticeProb.Gauss.MultivariateDensity
import LatticeProb.Prob.NormalComparisonCovariance

open MeasureTheory ProbabilityTheory Matrix

namespace LatticeProb

end LatticeProb
