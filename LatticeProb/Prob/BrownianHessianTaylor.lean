/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianHessianGenerator.lean, BouRabeeGwynne/BrownianTaylorBound.lean.
-/

import LatticeProb.Prob.BrownianIncrementMoments
import LatticeProb.Analysis.HarmonicBridge
import LatticeProb.Analysis.HessianTaylorRemainder
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hessian and Taylor expectations for standard Brownian motion

For a standard Brownian law on paths `ℝ≥0 → Euc d`, the coordinates of the path at a fixed time
`t` are independent centred Gaussians with variance `t`. This file integrates the second
derivative of a function along the path at a fixed time: the expectation of the quadratic Taylor
term is `t Δ f`, so it vanishes at every point where `f` is harmonic. It also gives the expectations of
the norm-squared and linear terms, and a one-step expectation bound for Taylor's formula under a
pointwise quadratic and quartic bound on the remainder.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian
open scoped NNReal ENNReal
namespace LatticeProb

/-- A bilinear form on `Euc d` is the sum of its values on the standard basis vectors, weighted
by the products of the coordinates of the two arguments. -/
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

/-- The squared Euclidean norm of a standard Brownian path at a fixed time is integrable. -/
lemma standardBrownianLaw_integrable_norm_sq {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    Integrable (fun ω ↦ ‖ω t‖ ^ 2) μ := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, pow_two]
  exact integrable_finsetSum _ (fun i _ ↦ standardBrownianLaw_integrable_coordinate_mul hμ t i i)

/-- The expectation of the squared Euclidean norm of a standard Brownian path at a fixed time
is `d` times `t`. -/
lemma standardBrownianLaw_integral_norm_sq {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    (∫ ω, ‖ω t‖ ^ 2 ∂μ) = (d : ℝ) * (t : ℝ) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, pow_two]
  rw [integral_finsetSum _ (fun i _ ↦ standardBrownianLaw_integrable_coordinate_mul hμ t i i)]
  simp [standardBrownianLaw_integral_coordinate_mul hμ]

/-- A continuous linear functional on `Euc d` is the sum of its values on the standard basis
vectors, weighted by the coordinates of the argument. -/
lemma continuousLinearMap_eq_sum_euclidean_coordinates {d : ℕ}
    (L : Euc d →L[ℝ] ℝ) (y : Euc d) :
    L y = ∑ i, y i * L (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  have hy : ∑ i, y i • EuclideanSpace.basisFun (Fin d) ℝ i = y :=
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr y
  calc
    L y = L (∑ i, y i • EuclideanSpace.basisFun (Fin d) ℝ i) := by rw [hy]
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

/-- A continuous linear functional of a standard Brownian path at a fixed time is integrable. -/
lemma standardBrownianLaw_integrable_linear {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (L : Euc d →L[ℝ] ℝ) : Integrable (fun ω ↦ L (ω t)) μ := by
  have heq : (fun ω : BrownianPath d ↦ L (ω t)) =
      fun ω ↦ ∑ i, ω t i * L (EuclideanSpace.basisFun (Fin d) ℝ i) :=
    funext (fun ω ↦ continuousLinearMap_eq_sum_euclidean_coordinates L (ω t))
  rw [heq]
  exact integrable_finsetSum _ (fun i _ ↦ ((hμ.2.1 i).integrable_eval t).mul_const _)

/-- A continuous linear functional of a standard Brownian path at a fixed time has expectation
zero. -/
lemma standardBrownianLaw_integral_linear {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) (L : Euc d →L[ℝ] ℝ) : (∫ ω, L (ω t) ∂μ) = 0 := by
  have heq : (fun ω : BrownianPath d ↦ L (ω t)) =
      fun ω ↦ ∑ i, ω t i * L (EuclideanSpace.basisFun (Fin d) ℝ i) :=
    funext (fun ω ↦ continuousLinearMap_eq_sum_euclidean_coordinates L (ω t))
  rw [heq]
  rw [integral_finsetSum _ (fun i _ ↦ ((hμ.2.1 i).integrable_eval t).mul_const _)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_mul_const, (hμ.2.1 i).integral_eval t, zero_mul]

/-- The second derivative of a function along a standard Brownian path at a fixed time is
integrable. No smoothness hypothesis is needed, since `fderiv` is total. -/
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
  exact integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦
    (standardBrownianLaw_integrable_coordinate_mul hμ t i j).const_mul _))

/-- One-step expectation bound for Taylor's formula along a standard Brownian path at a fixed
time. If the Taylor remainder of a `C²` function `f` at `x` is bounded by `ε ‖y‖ ^ 2 + C ‖y‖ ^ 4`,
then the expectation of `f (x + ω t)` differs from `f x + (t / 2) Δ f x` by at most
`ε d t + C (3 d² t²)`. Here `f` is continuous, and the constants `ε` and `C` are nonnegative. -/
theorem standardBrownianLaw_taylor_expectation_bound {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (t : ℝ≥0) {f : Euc d → ℝ} (hf : Continuous f) (x : Euc d)
    {ε C : ℝ} (_hε : 0 ≤ ε) (hC : 0 ≤ C)
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

namespace BrownianHessianTaylorExample

/-- The coordinate expansion of the bilinear form `innerₗ` on `Euc 2`, a concrete bilinear map. -/
theorem innerₗ_eq_sum_coordinates (y z : Euc 2) :
    innerₗ (Euc 2) y z = ∑ i, ∑ j,
      innerₗ (Euc 2) (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j) *
        (y i * z j) :=
  bilinear_eq_sum_euclidean_coordinates (innerₗ (Euc 2)) y z

/-- The product of the first two coordinates is harmonic on all of `Euc 2`: its Hessian is the
constant bilinear form `M`, whose trace vanishes. -/
theorem prod_coord_isHarmonicOn : IsHarmonicOn (fun y : Euc 2 ↦ y 0 * y 1) Set.univ := by
  let p0 : Euc 2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : Euc 2 →L[ℝ] ℝ := EuclideanSpace.proj 1
  let M : Euc 2 →L[ℝ] (Euc 2 →L[ℝ] ℝ) := p0.smulRight p1 + p1.smulRight p0
  have hd (y : Euc 2) : HasFDerivAt (fun y : Euc 2 ↦ y 0 * y 1) (M y) y := by
    refine ((p0.hasFDerivAt (x := y)).mul (p1.hasFDerivAt (x := y))).congr_fderiv ?_
    ext v
    simp [M, p0, p1]
  have hfd : fderiv ℝ (fun y : Euc 2 ↦ y 0 * y 1) = ⇑M := funext fun y ↦ (hd y).fderiv
  refine ⟨(p0.contDiff.mul p1.contDiff).contDiffOn, fun x _ ↦ ?_⟩
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [iteratedFDeriv_two_apply, hfd, ContinuousLinearMap.fderiv]
  simp [M, p0, p1, Fin.sum_univ_two, EuclideanSpace.basisFun_apply,]

/-- Nonvacuity of the Hessian identity: for any standard Brownian law on `Euc 2` paths, the
expected Hessian term of `y ↦ y 0 * y 1` at any point vanishes. -/
theorem prod_coord_integral_hessian_eq_zero {μ : Measure (BrownianPath 2)}
    (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) (x : Euc 2) :
    (∫ ω, fderiv ℝ (fderiv ℝ (fun y : Euc 2 ↦ y 0 * y 1)) x (ω t) (ω t) ∂μ) = 0 :=
  standardBrownianLaw_integral_hessian_eq_zero hμ t prod_coord_isHarmonicOn (Set.mem_univ x)

end BrownianHessianTaylorExample

end LatticeProb
