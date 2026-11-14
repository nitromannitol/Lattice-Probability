import LatticeProb.Analysis.WeakLaplaceMollify
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Sub-mean-value inequalities and the distributional Laplacian

Integration by parts for the Laplacian and its application to functions satisfying the
sub-mean-value property.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped InnerProductSpace ContDiff Convolution
open Laplacian

namespace LatticeProb.Ishii

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

private theorem integral_mul_fderiv_eq_neg {f φ : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : E) :
    ∫ x, f x * fderiv ℝ φ x v ∂μ = -∫ x, fderiv ℝ f x v * φ x ∂μ := by
  have hfc : Continuous fun x => fderiv ℝ f x v :=
    (LatticeProb.PegdenSmart.contDiff_fderiv_apply hf v).continuous
  have hφc : Continuous fun x => fderiv ℝ φ x v :=
    (LatticeProb.PegdenSmart.contDiff_fderiv_apply hφ v).continuous
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hφ.differentiable (by simp) x)
  · exact (hfc.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hf.continuous.mul hφc).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left
  · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left

private theorem integral_mul_fderiv_fderiv_eq {f φ : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (v : E) :
    ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ φ y v) x v ∂μ =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v * φ x ∂μ := by
  have h1 := integral_mul_fderiv_eq_neg (μ := μ) (φ := fun y => fderiv ℝ φ y v) hf
    (LatticeProb.PegdenSmart.contDiff_fderiv_apply hφ v) (hc.fderiv_apply ℝ v) v
  have h2 := integral_mul_fderiv_eq_neg (μ := μ) (f := fun y => fderiv ℝ f y v)
    (LatticeProb.PegdenSmart.contDiff_fderiv_apply hf v) hφ hc v
  rw [h1, h2, neg_neg]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem laplacian_eq_sum_fderiv {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ f = fun x => ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ E i)) x
      (stdOrthonormalBasis ℝ E i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext x
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const (stdOrthonormalBasis ℝ E i))]
  simp

/-- Integration by parts for the Laplacian against a compactly supported smooth function. -/
theorem integral_mul_laplacian_eq {f φ : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ x, f x * Δ φ x ∂μ = ∫ x, Δ f x * φ x ∂μ := by
  let b := stdOrthonormalBasis ℝ E
  have hi : ∀ i, Integrable (fun x => f x *
      fderiv ℝ (fun y => fderiv ℝ φ y (b i)) x (b i)) μ := fun i =>
    (hf.continuous.mul (LatticeProb.PegdenSmart.contDiff_fderiv_apply
      (LatticeProb.PegdenSmart.contDiff_fderiv_apply hφ _) _).continuous)
      |>.integrable_of_hasCompactSupport (((hc.fderiv_apply ℝ _).fderiv_apply ℝ _).mul_left)
  have hj : ∀ i, Integrable (fun x =>
      fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) * φ x) μ := fun i =>
    ((LatticeProb.PegdenSmart.contDiff_fderiv_apply
      (LatticeProb.PegdenSmart.contDiff_fderiv_apply hf _) _).continuous.mul hφ.continuous)
      |>.integrable_of_hasCompactSupport hc.mul_left
  rw [laplacian_eq_sum_fderiv hφ, laplacian_eq_sum_fderiv hf]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => hi i, integral_finsetSum _ fun i _ => hj i]
  exact Finset.sum_congr rfl fun i _ => integral_mul_fderiv_fderiv_eq hf hφ hc (b i)

/-- A smooth function whose Laplacian is nonnegative on the support of a nonnegative test
function has nonnegative distributional Laplacian against that test. -/
theorem integral_mul_laplacian_nonneg_of_laplacian_nonneg {f φ : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hf0 : ∀ x ∈ tsupport φ, 0 ≤ Δ f x) :
    0 ≤ ∫ x, f x * Δ φ x ∂μ := by
  rw [integral_mul_laplacian_eq hf hφ hc]
  apply integral_nonneg
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact mul_nonneg (hf0 x hx) (hφ0 x)
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [Pi.zero_apply, hφx, mul_zero, le_refl]

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- In a zero-dimensional space, the distributional Laplacian vanishes. -/
theorem integral_mul_laplacian_eq_zero_of_subsingleton [Subsingleton E] (f φ : E → ℝ) :
    ∫ x, f x * Δ φ x ∂μ = 0 := by
  have hφ : φ = fun _ => φ 0 := funext fun x => congrArg φ (Subsingleton.elim x 0)
  rw [hφ]
  simp

end LatticeProb.Ishii
