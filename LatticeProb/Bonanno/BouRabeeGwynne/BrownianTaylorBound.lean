/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianTaylorBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianHessianGenerator

/-!
# Actual one-step harmonic Taylor error for Brownian motion

A pointwise C² Taylor remainder controlled by a small quadratic term and a
quartic tail gives an explicit expectation error. The distribution, covariance,
and moments are those of the actual standard Brownian law. The analytic
remainder estimate is stated pointwise, not as an assumed convergence transfer.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian
open scoped NNReal ENNReal
namespace BouRabeeGwynne

lemma standardBrownianLaw_integrable_norm_sq {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    Integrable (fun ω ↦ ‖ω t‖ ^ 2) μ := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, pow_two]
  exact integrable_finset_sum _ (fun i _ ↦ standardBrownianLaw_integrable_coordinate_mul hμ t i i)

lemma standardBrownianLaw_integral_norm_sq {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    (∫ ω, ‖ω t‖ ^ 2 ∂μ) = (d : ℝ) * (t : ℝ) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, pow_two]
  rw [integral_finset_sum _ (fun i _ ↦ standardBrownianLaw_integrable_coordinate_mul hμ t i i)]
  simp [standardBrownianLaw_integral_coordinate_mul hμ]

lemma continuousLinearMap_eq_sum_euclidean_coordinates {d : ℕ}
    (L : Euc d →L[ℝ] ℝ) (y : Euc d) :
    L y = ∑ i, y i * L (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  have hy : ∑ i, y i • EuclideanSpace.basisFun (Fin d) ℝ i = y :=
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr y
  calc
    L y = L (∑ i, y i • EuclideanSpace.basisFun (Fin d) ℝ i) := by rw [hy]
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

lemma standardBrownianLaw_integrable_linear {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (L : Euc d →L[ℝ] ℝ) : Integrable (fun ω ↦ L (ω t)) μ := by
  have heq : (fun ω : BrownianPath d ↦ L (ω t)) =
      fun ω ↦ ∑ i, ω t i * L (EuclideanSpace.basisFun (Fin d) ℝ i) :=
    funext (fun ω ↦ continuousLinearMap_eq_sum_euclidean_coordinates L (ω t))
  rw [heq]
  exact integrable_finset_sum _ (fun i _ ↦ ((hμ.2.1 i).integrable_eval t).mul_const _)

lemma standardBrownianLaw_integral_linear {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (L : Euc d →L[ℝ] ℝ) : (∫ ω, L (ω t) ∂μ) = 0 := by
  have heq : (fun ω : BrownianPath d ↦ L (ω t)) =
      fun ω ↦ ∑ i, ω t i * L (EuclideanSpace.basisFun (Fin d) ℝ i) :=
    funext (fun ω ↦ continuousLinearMap_eq_sum_euclidean_coordinates L (ω t))
  rw [heq]
  rw [integral_finset_sum _ (fun i _ ↦ ((hμ.2.1 i).integrable_eval t).mul_const _)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_mul_const, (hμ.2.1 i).integral_eval t, zero_mul]

lemma standardBrownianLaw_integrable_hessian {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (f : Euc d → ℝ) (x : Euc d) :
    Integrable (fun ω ↦ fderiv ℝ (fderiv ℝ f) x (ω t) (ω t)) μ := by
  let H := bilinearIteratedFDerivTwo ℝ f x
  have heq : (fun ω : BrownianPath d ↦ fderiv ℝ (fderiv ℝ f) x (ω t) (ω t)) =
      fun ω ↦ ∑ i, ∑ j,
        H (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j) *
          (ω t i * ω t j) :=
    funext (fun ω ↦ bilinear_eq_sum_euclidean_coordinates H (ω t) (ω t))
  rw [heq]
  exact integrable_finset_sum _ (fun i _ ↦ integrable_finset_sum _ (fun j _ ↦
    (standardBrownianLaw_integrable_coordinate_mul hμ t i j).const_mul _))

/-- The one-step Gaussian generator estimate for an actual Taylor remainder.
Uniform C² continuity supplies epsilon and the quartic-tail constant on the
compact neighborhood used in the stopped harmonic argument. -/
theorem standardBrownianLaw_taylor_expectation_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) {f : Euc d → ℝ} (hf : Continuous f) (x : Euc d)
    {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hR : ∀ y : Euc d,
      |f (x + y) - f x - fderiv ℝ f x y - (1 / 2 : ℝ) *
        fderiv ℝ (fderiv ℝ f) x y y| ≤ ε * ‖y‖ ^ 2 + C * ‖y‖ ^ 4) :
    |(∫ ω, f (x + ω t) ∂μ) - f x - (t : ℝ) / 2 * Δ f x| ≤
      ε * (d : ℝ) * (t : ℝ) + C * (3 * (d : ℝ) ^ 2 * (t : ℝ) ^ 2) := by
  letI : IsProbabilityMeasure μ := hμ.1
  let R : BrownianPath d → ℝ := fun ω ↦ f (x + ω t) - f x -
    fderiv ℝ f x (ω t) - (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x (ω t) (ω t)
  have hg : Integrable (fun ω : BrownianPath d ↦ ε * ‖ω t‖ ^ 2 + C * ‖ω t‖ ^ 4) μ :=
    ((standardBrownianLaw_integrable_norm_sq hμ t).const_mul ε).add
      ((standardBrownianLaw_integrable_norm_fourth hμ t).const_mul C)
  have hmR : AEStronglyMeasurable R μ := by dsimp [R]; fun_prop
  have hbound : ∀ ω, ‖R ω‖ ≤ ε * ‖ω t‖ ^ 2 + C * ‖ω t‖ ^ 4 := fun ω ↦ hR (ω t)
  have hiR : Integrable R μ := hg.mono' hmR (Filter.Eventually.of_forall hbound)
  have hiL := standardBrownianLaw_integrable_linear hμ t (fderiv ℝ f x)
  have hiQ := (standardBrownianLaw_integrable_hessian hμ t f x).const_mul (1 / 2 : ℝ)
  have hif : Integrable (fun ω : BrownianPath d ↦ f (x + ω t)) μ := by
    have h := ((hiR.add (integrable_const (f x))).add hiL).add hiQ
    exact h.congr (Filter.Eventually.of_forall (fun ω ↦ by dsimp [R]; ring))
  have hmean : (∫ ω, R ω ∂μ) =
      (∫ ω, f (x + ω t) ∂μ) - f x - (t : ℝ) / 2 * Δ f x := by
    have hsub1 : (∫ ω, f (x + ω t) - f x ∂μ) = (∫ ω, f (x + ω t) ∂μ) - f x := by
      simpa only [integral_const, probReal_univ, one_smul] using
        integral_sub hif (integrable_const (f x))
    have hsub2 : (∫ ω, f (x + ω t) - f x - fderiv ℝ f x (ω t) ∂μ) =
        (∫ ω, f (x + ω t) ∂μ) - f x := by
      calc
        _ = (∫ ω, f (x + ω t) - f x ∂μ) - (∫ ω, fderiv ℝ f x (ω t) ∂μ) :=
          integral_sub (hif.sub (integrable_const (f x))) hiL
        _ = _ := by rw [hsub1, standardBrownianLaw_integral_linear hμ, sub_zero]
    calc
      _ = (∫ ω, f (x + ω t) - f x - fderiv ℝ f x (ω t) ∂μ) -
          (∫ ω, (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) x (ω t) (ω t) ∂μ) :=
        integral_sub ((hif.sub (integrable_const (f x))).sub hiL) hiQ
      _ = _ := by
        rw [hsub2, integral_const_mul, standardBrownianLaw_integral_hessian hμ]
        ring
  rw [← hmean, ← Real.norm_eq_abs]
  calc
    ‖∫ ω, R ω ∂μ‖ ≤ ∫ ω, ε * ‖ω t‖ ^ 2 + C * ‖ω t‖ ^ 4 ∂μ :=
      norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)
    _ = ε * ((d : ℝ) * (t : ℝ)) + C * (∫ ω, ‖ω t‖ ^ 4 ∂μ) := by
      rw [integral_add ((standardBrownianLaw_integrable_norm_sq hμ t).const_mul ε)
        ((standardBrownianLaw_integrable_norm_fourth hμ t).const_mul C),
        integral_const_mul, integral_const_mul, standardBrownianLaw_integral_norm_sq hμ]
    _ ≤ _ := add_le_add (le_of_eq (by ring)) (mul_le_mul_of_nonneg_left
      (standardBrownianLaw_integral_norm_fourth_le hμ t) hC)

end BouRabeeGwynne
