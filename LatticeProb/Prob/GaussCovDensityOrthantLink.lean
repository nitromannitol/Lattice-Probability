/-
# The Gaussian orthant probability as an integral of `covDensity` over `Set.Iic b`

Li--Shao normal comparison, assembly (route items 3 and 8).  The derivative packet works with

  `F(t) = ∫ x in Set.Iic b, covDensity (S_t) x`  on `Fin n → ℝ`,

while the frozen statement is about the law `multivariateGaussian 0 S` on
`EuclideanSpace ℝ (Fin n)` and the orthant `{y | ∀ i, y i ≤ b i}`.  This file links the two:

* `multivariateGaussian_orthant_eq_lintegral` : the orthant mass is the lower integral of
  `ENNReal.ofReal (covDensity S)` over `Set.Iic b`;
* `multivariateGaussian_orthant_toReal_eq` : its real part is `∫ x in Set.Iic b, covDensity S x`.

Route.  `multivariateGaussian_eq_withDensity_covDensity` turns the law into a `withDensity`, whose
value on the (measurable) orthant is a set lintegral; `lintegral_orthant_eq` transports that to
`Set.Iic b` along the volume-preserving `WithLp.toLp 2`.  The real form is
`integral_eq_lintegral_of_nonneg_ae` with `0 ≤ covDensity S` (`covDensity_pos`).
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensityIntegrable
import LatticeProb.Prob.NormalComparisonOrthantSigned
import LatticeProb.Prob.NormalComparisonOrthantDeriv

open MeasureTheory ProbabilityTheory Matrix

namespace LatticeProb

section OrthantLink

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}

/-- The density `covDensity S` is continuous. -/
private lemma continuous_covDensity_link (S : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (covDensity S) := by
  unfold covDensity
  have h : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (S⁻¹ *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  fun_prop

/-- The orthant `{y | ∀ i, y i ≤ b i}` of `EuclideanSpace ℝ (Fin n)` is measurable. -/
private lemma measurableSet_orthant_link (b : Fin n → ℝ) :
    MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i} := by
  rw [show {y : EuclideanSpace ℝ (Fin n) | ∀ i, y i ≤ b i}
      = ⋂ i, {y : EuclideanSpace ℝ (Fin n) | y i ≤ b i} by
    ext y; simp]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le (by fun_prop : Measurable fun y : EuclideanSpace ℝ (Fin n) => y i)
      measurable_const

/-- **The orthant mass of `N(0, S)` as a lower integral of the density.**  The law
`multivariateGaussian 0 S` of the orthant `{y | ∀ i, y i ≤ b i}` is the lower integral of
`ENNReal.ofReal (covDensity S)` over `Set.Iic b ⊆ Fin n → ℝ`. -/
theorem multivariateGaussian_orthant_eq_lintegral (hS : S.PosDef) (b : Fin n → ℝ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S {y | ∀ i, y i ≤ b i}
      = ∫⁻ x in Set.Iic b, ENNReal.ofReal (covDensity S x) := by
  have hf : Measurable
      (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (covDensity S (WithLp.ofLp y))) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_covDensity_link S).comp (PiLp.continuous_ofLp 2 _)).measurable
  rw [multivariateGaussian_eq_withDensity_covDensity S hS,
    withDensity_apply _ (measurableSet_orthant_link b),
    lintegral_orthant_eq b
      (fun y => ENNReal.ofReal (covDensity S (WithLp.ofLp y))) hf]

/-- **The orthant mass of `N(0, S)` as an integral of the density.**  The real mass of the
orthant `{y | ∀ i, y i ≤ b i}` under `multivariateGaussian 0 S` is
`∫ x in Set.Iic b, covDensity S x`. -/
theorem multivariateGaussian_orthant_toReal_eq (hS : S.PosDef) (b : Fin n → ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S {y | ∀ i, y i ≤ b i}).toReal
      = ∫ x in Set.Iic b, covDensity S x := by
  rw [multivariateGaussian_orthant_eq_lintegral hS b,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => (covDensity_pos hS x).le)
      (continuous_covDensity_link S).aestronglyMeasurable]

end OrthantLink

end LatticeProb
