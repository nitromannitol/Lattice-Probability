/-
# The scalar covariance `v I`: the Gaussian density and the orthant probability factor

Li--Shao normal comparison, assembly (route item 8, the `t = 0` endpoint).  At `t = 0` the smart
path is the scalar matrix `v • 1`, and the frozen statement subtracts
`∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal`.  This file proves, for `0 < v`:

* `posDef_scalar_one` : `v • 1` is positive definite;
* `covDensity_scalar` : `covDensity (v • 1) x = ∏ i, gaussianPDFReal 0 v (x i)`;
* `multivariateGaussian_orthant_scalar` : the orthant mass of `N(0, v I)` with per-coordinate
  bounds `b i` is the product of the one-dimensional masses
  `∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal`.

Route.  `covDensity_scalar` is algebra: `det (v • 1) = v ^ n`, `(v • 1)⁻¹ = v⁻¹ • 1`, and the
exponent `x ⬝ᵥ (v⁻¹ • 1 *ᵥ x) = v⁻¹ * ∑ (x i)^2`.  The orthant statement is
`multivariateGaussian_orthant_toReal_eq`, the product form of the density, the identification of
`Set.Iic b` with `Set.pi univ (fun i => Set.Iic (b i))`, `Measure.restrict_pi_pi`, and
`integral_fintype_prod_eq_prod`.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensityOrthantLink
import LatticeProb.Prob.GaussCovDensityIntegrable

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace LatticeProb

section Scalar

variable {n : ℕ} {v : ℝ≥0}

/-- The scalar matrix `v • 1` is positive definite for `0 < v`. -/
theorem posDef_scalar_one (hv : 0 < v) :
    ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast hv)

/-- The inverse of the scalar matrix `v • 1` is `v⁻¹ • 1`. -/
theorem inv_scalar_one (hv : 0 < v) :
    ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = (v : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  refine Matrix.inv_eq_right_inv ?_
  rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hv', one_smul]

/-- The exponent of the density at the scalar matrix: `x ⬝ᵥ (v⁻¹ • 1) *ᵥ x = v⁻¹ * ∑ (x i)^2`. -/
theorem dotProduct_inv_scalar_one (x : Fin n → ℝ) :
    x ⬝ᵥ (((v : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) = (v : ℝ)⁻¹ * ∑ i, x i ^ 2 := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  simp [dotProduct, pow_two]

/-- The normalising constant of the density at the scalar matrix is the `n`-th power of the
one-dimensional one. -/
theorem covDensity_scalar_const (hv : 0 < v) :
    (2 * Real.pi) ^ (-(n : ℝ) / 2) * (((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det) ^
        (-(1 : ℝ) / 2)
      = ((√(2 * Real.pi * v))⁻¹) ^ n := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity [Real.pi_pos]
  have e1 : (√(2 * Real.pi * v))⁻¹ = (2 * Real.pi) ^ (-(1 / 2 : ℝ)) * (v : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), Real.mul_rpow h2pi.le hv'.le]
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, e1, mul_pow,
    ← Real.rpow_mul_natCast h2pi.le, ← Real.rpow_mul_natCast hv'.le,
    ← Real.rpow_natCast_mul hv'.le]
  congr 2 <;> ring

/-- The density of N(0, v I) is the product of the one-dimensional Gaussian densities. -/
theorem covDensity_scalar (hv : 0 < v) (x : Fin n → ℝ) :
    covDensity ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) x = ∏ i, gaussianPDFReal 0 v (x i) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  unfold covDensity
  rw [inv_scalar_one hv, dotProduct_inv_scalar_one, covDensity_scalar_const hv]
  simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-- `Set.Iic b` as a product of the coordinate half-lines, restricted volume as a product
measure: the integral over `Set.Iic b` of a product of functions of single coordinates. -/
theorem integral_Iic_prod (f : ℝ → ℝ) (b : Fin n → ℝ) :
    ∫ x in Set.Iic b, ∏ i, f (x i) = ∏ i, ∫ y in Set.Iic (b i), f y := by
  rw [← Set.pi_univ_Iic b, volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (fun _ => f)

/-- The one-dimensional Gaussian mass of a half-line as an integral of the density. -/
theorem gaussianReal_Iic_toReal (hv : 0 < v) (c : ℝ) :
    (gaussianReal 0 v (Set.Iic c)).toReal = ∫ y in Set.Iic c, gaussianPDFReal 0 v y := by
  rw [gaussianReal_apply_eq_integral 0 hv.ne' (Set.Iic c)]
  exact ENNReal.toReal_ofReal
    (integral_nonneg fun y => gaussianPDFReal_nonneg 0 v y)

/-- The orthant probability of N(0, v I) is the product of the marginal probabilities. -/
theorem multivariateGaussian_orthant_scalar (hv : 0 < v) (b : Fin n → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        ((v : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) {y | ∀ i, y i ≤ b i}).toReal
      = ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal := by
  rw [multivariateGaussian_orthant_toReal_eq (posDef_scalar_one hv) b]
  simp_rw [covDensity_scalar hv]
  rw [integral_Iic_prod (gaussianPDFReal 0 v) b]
  exact Finset.prod_congr rfl fun i _ => (gaussianReal_Iic_toReal hv (b i)).symm

end Scalar

end LatticeProb
