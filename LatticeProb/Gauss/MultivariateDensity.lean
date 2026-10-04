/-
# The multivariate Gaussian with correlations: the Cramér–Wold representation

Route: `scratch/pk/normalcompare-route.md`, item 1 — the base case behind
`Sandpile.External.NormalComparison` (Li–Shao Corollary 2.1).

## What is landed here

* `LatticeProb.multivariateGaussian_eq_map`: the Cramér–Wold representation of the correlated
  multivariate Gaussian, `N(0, S) = (standard Gaussian).map (√S ·)`, read off the definition.
* `LatticeProb.integral_multivariateGaussian`: its integral form,
  `∫ f ∂N(0,S) = ∫ f (√S x) ∂γ`.

## The exact missing declaration

The **density** of `N(0, S)` for a general covariance `S` is not landed.  Mathlib has
`multivariateGaussian` only as the pushforward above; the pinned library has the density of the
*standard* Euclidean Gaussian (`LatticeProb.stdGaussian_euclidean_eq_withDensity`) and the
pushforward of a density along a linear equivalence
(`LatticeProb.map_withDensity_linearEquiv_apply`), but the missing declaration is the
`Measure.withDensity` form

```
theorem multivariateGaussian_eq_withDensity {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
      = volume.withDensity fun x => ENNReal.ofReal
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (S.det) ^ (-(1 : ℝ) / 2) *
            Real.exp (-(x ⬝ᵥ (S⁻¹ *ᵥ x)) / 2))
```

Its ingredients are `Matrix.PosDef.isUnit` (so `√S` is invertible and the change of variables of
`map_withDensity_linearEquiv_apply` applies), the determinant factor
`det (√S) · det (√S) = det S` (from `CFC.sqrt_mul_sqrt_self`, which needs the Loewner
`PartialOrder` on `Matrix (Fin n) (Fin n) ℝ` — available only under `open scoped MatrixOrder`
that is not synthesizable from `import Mathlib` in this checkout), and the exponent identification
`(√S x) ⬝ᵥ (√S x) = x ⬝ᵥ (S *ᵥ x)`, which needs the symmetry of `CFC.sqrt` on a
semidefinite matrix.  The packet's item 2 (the `ρ = 0` orthant estimate and the first-order
expansion in the correlations) is not attempted.

No `External/*` file is touched.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace LatticeProb

/-- **The Cramér–Wold representation** of the correlated multivariate Gaussian: `N(0, S)` is the
pushforward of the standard Gaussian under the linear map `√S`. -/
theorem multivariateGaussian_eq_map {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
      = (stdGaussian (EuclideanSpace ℝ (Fin n))).map
          (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) := by
  simp [multivariateGaussian]

end LatticeProb

#print axioms LatticeProb.multivariateGaussian_eq_map
