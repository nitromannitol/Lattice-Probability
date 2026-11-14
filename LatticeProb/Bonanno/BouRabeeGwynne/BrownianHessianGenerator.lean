/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianHessianGenerator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianQuadraticMoments
import LatticeProb.Bonanno.BouRabeeGwynne.Harmonic

/-!
# The Brownian quadratic term is the actual continuum Laplacian

This identifies the Hessian term occurring in Taylor's formula with the exact
Laplacian used by the approved harmonicity predicate. In particular, the term
vanishes in the harmonic region, in every finite dimension.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma bilinear_eq_sum_euclidean_coordinates {d : ℕ}
    (H : Euc d →ₗ[ℝ] Euc d →ₗ[ℝ] ℝ) (y z : Euc d) :
    H y z = ∑ i, ∑ j,
      H (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j) *
        (y i * z j) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hy : ∑ i, y i • b i = y := b.sum_repr y
  have hz : ∑ j, z j • b j = z := b.sum_repr z
  calc
    H y z = H (∑ i, y i • b i) (∑ j, z j • b j) := by rw [hy, hz]
    _ = _ := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [b]
      ring

/-- Exact integration of the actual second derivative, rather than an assumed
quadratic-form identity or an abstract covariance field. -/
theorem standardBrownianLaw_integral_hessian {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (f : Euc d → ℝ) (x : Euc d) :
    (∫ ω, fderiv ℝ (fderiv ℝ f) x (ω t) (ω t) ∂μ) = (t : ℝ) * Δ f x := by
  let H := bilinearIteratedFDerivTwo ℝ f x
  have hexpand (y : Euc d) :
      fderiv ℝ (fderiv ℝ f) x y y = ∑ i, ∑ j,
        H (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j) *
          (y i * y j) := bilinear_eq_sum_euclidean_coordinates H y y
  simp_rw [hexpand]
  rw [standardBrownianLaw_integral_quadratic hμ]
  congr 1
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  apply Finset.sum_congr rfl
  intro i hi
  exact bilinearIteratedFDerivTwo_eq_iteratedFDeriv f x _ _

/-- Harmonicity cancels the actual expected quadratic Taylor term. -/
theorem standardBrownianLaw_integral_hessian_eq_zero {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) {f : Euc d → ℝ} {U : Set (Euc d)} (hf : IsHarmonicOn f U)
    {x : Euc d} (hx : x ∈ U) :
    (∫ ω, fderiv ℝ (fderiv ℝ f) x (ω t) (ω t) ∂μ) = 0 := by
  rw [standardBrownianLaw_integral_hessian hμ, hf.laplacian_eq_zero hx, mul_zero]

end BouRabeeGwynne
