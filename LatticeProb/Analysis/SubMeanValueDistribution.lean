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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integrable_of_continuousOn_compact {g : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hg : ContinuousOn g K) (h0 : ∀ x ∉ K, g x = 0) :
    Integrable g μ :=
  (hg.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero h0

/-- Uniform convergence on the support of a compactly supported test function passes through
integration against its Laplacian. -/
theorem tendsto_integral_mul_laplacian_of_tendstoUniformlyOn {f : ℕ → E → ℝ}
    {g φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hunif : TendstoUniformlyOn f g atTop (tsupport φ))
    (hcont : ∀ᶠ n in atTop, ContinuousOn (f n) (tsupport φ)) :
    Tendsto (fun n => ∫ x, f n x * Δ φ x ∂μ) atTop (𝓝 (∫ x, g x * Δ φ x ∂μ)) := by
  have hΔ : Continuous (Δ φ) := by
    rw [laplacian_eq_sum_fderiv hφ]
    exact continuous_finsetSum _ fun i _ =>
      (LatticeProb.PegdenSmart.contDiff_fderiv_apply
        (LatticeProb.PegdenSmart.contDiff_fderiv_apply hφ _) _).continuous
  have hΔ0 : ∀ x ∉ tsupport φ, Δ φ x = 0 := by
    intro x hx
    have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.1 hx
    rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
    simp
  have hg : ContinuousOn g (tsupport φ) := hunif.continuousOn hcont.frequently
  refine tendsto_integral_filter_of_dominated_convergence (fun x => (|g x| + 1) * |Δ φ x|)
    ?_ ?_ ?_ ?_
  · filter_upwards [hcont] with n hn
    exact (integrable_of_continuousOn_compact hc (hn.mul hΔ.continuousOn)
      fun x hx => by simp [hΔ0 x hx]).aestronglyMeasurable
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif 1 one_pos] with n hn
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport φ
    · have h1 : dist (g x) (f n x) < 1 := hn x hx
      rw [Real.dist_eq, abs_sub_comm] at h1
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have := abs_sub_abs_le_abs_sub (f n x) (g x)
      linarith
    · simp [hΔ0 x hx]
  · exact integrable_of_continuousOn_compact hc
      ((hg.abs.add continuousOn_const).mul hΔ.abs.continuousOn) fun x hx => by simp [hΔ0 x hx]
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport φ
    · exact (hunif.tendsto_at hx).mul_const _
    · simp [hΔ0 x hx]

/-- The distributional inequality is preserved by locally uniform limits of smooth functions
with nonnegative Laplacian on the support of the test function. -/
theorem integral_mul_laplacian_nonneg_of_smooth_approximation {f : ℕ → E → ℝ}
    {g φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hf0 : ∀ᶠ n in atTop, ∀ x ∈ tsupport φ, 0 ≤ Δ (f n) x)
    (hunif : TendstoUniformlyOn f g atTop (tsupport φ)) :
    0 ≤ ∫ x, g x * Δ φ x ∂μ := by
  have hlim := tendsto_integral_mul_laplacian_of_tendstoUniformlyOn (μ := μ) hφ hc hunif
    (Filter.Eventually.of_forall fun n => (hf n).continuous.continuousOn)
  exact ge_of_tendsto hlim (hf0.mono fun n hn =>
    integral_mul_laplacian_nonneg_of_laplacian_nonneg (hf n) hφ hc hφ0 hn)

end LatticeProb.Ishii
