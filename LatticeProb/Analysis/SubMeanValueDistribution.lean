import LatticeProb.Analysis.WeakLaplaceMollify
import LatticeProb.Analysis.HessianTaylorRemainder
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

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

omit [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem exists_smooth_extension_near_compact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ (g : E → ℝ) (V : Set E), IsOpen V ∧ K ⊆ V ∧ ContDiff ℝ ∞ g ∧ EqOn g f V := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨O, hO, hLO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hL hU hLU
  obtain ⟨χ, hχ, _, hχsupp, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := modelWithCornersSelf ℝ E) (n := ⊤)
      hO hL.isClosed hLO
  have hχs : ContDiff ℝ ∞ χ := contMDiff_iff_contDiff.mp hχ
  let g : E → ℝ := fun x => χ x * f x
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχs.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · have hxO : x ∈ (closure O)ᶜ := fun hx' => hx (hOU hx')
      have heq : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxO] with y hy
        have hyO : y ∉ O := fun hy' => hy (subset_closure hy')
        have hχzero : χ y = 0 := by
          apply Function.notMem_support.mp
          simpa only [hχsupp] using hyO
        exact mul_eq_zero_of_left hχzero _
      exact contDiffAt_const.congr_of_eventuallyEq heq
  refine ⟨g, interior L, isOpen_interior, hKL, hg, ?_⟩
  intro x hx
  change χ x * f x = f x
  rw [(hχone x).mp (interior_subset hx), one_mul]

/-- Local smoothness and a nonnegative Laplacian near the support imply the distributional
inequality against a nonnegative test function. -/
theorem integral_mul_laplacian_nonneg_of_contDiffOn {U : Set E} (hU : IsOpen U)
    {f φ : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (hφ0 : ∀ x, 0 ≤ φ x)
    (hf0 : ∀ x ∈ tsupport φ, 0 ≤ Δ f x) :
    0 ≤ ∫ x, f x * Δ φ x ∂μ := by
  obtain ⟨g, V, hV, hKV, hg, heq⟩ := exists_smooth_extension_near_compact hc hU hφU hf
  have hg0 : ∀ x ∈ tsupport φ, 0 ≤ Δ g x := by
    intro x hx
    have hev : g =ᶠ[𝓝 x] f := by
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      exact heq hy
    rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
    exact hf0 x hx
  have h := integral_mul_laplacian_nonneg_of_laplacian_nonneg (μ := μ) hg hφ hc hφ0 hg0
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport φ
  · rw [heq (hKV hx)]
  · have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.1 hx
    have hΔ : Δ φ x = 0 := by
      rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
      simp
    simp [hΔ]

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

/-- The distributional inequality is preserved by uniform limits of functions that are smooth
with nonnegative Laplacian near the test function's support. -/
theorem integral_mul_laplacian_nonneg_of_local_smooth_approximation {f : ℕ → E → ℝ}
    {g φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x)
    (hf : ∀ᶠ n in atTop, ∃ U : Set E, IsOpen U ∧ tsupport φ ⊆ U ∧
      ContDiffOn ℝ ∞ (f n) U ∧ ∀ x ∈ tsupport φ, 0 ≤ Δ (f n) x)
    (hunif : TendstoUniformlyOn f g atTop (tsupport φ)) :
    0 ≤ ∫ x, g x * Δ φ x ∂μ := by
  have hcont : ∀ᶠ n in atTop, ContinuousOn (f n) (tsupport φ) := by
    filter_upwards [hf] with n ⟨U, hU, hφU, hn, hn0⟩
    exact hn.continuousOn.mono hφU
  have hlim := tendsto_integral_mul_laplacian_of_tendstoUniformlyOn (μ := μ) hφ hc hunif hcont
  apply ge_of_tendsto hlim
  filter_upwards [hf] with n ⟨U, hU, hφU, hn, hn0⟩
  exact integral_mul_laplacian_nonneg_of_contDiffOn (μ := μ) hU hn hφ hc hφU hφ0 hn0

/-- A nonnegative Laplacian for sufficiently fine mollifications implies the distributional
inequality. -/
theorem integral_mul_laplacian_nonneg_of_mollify {U : Set E} (hU : IsOpen U)
    {u φ : E → ℝ} (hu : ContinuousOn u U) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (hφ0 : ∀ x, 0 ≤ φ x)
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {ρ : ℕ → E → ℝ} (hρs : ∀ n, ContDiff ℝ ∞ (ρ n))
    (hρc : ∀ n, HasCompactSupport (ρ n)) (hρ0 : ∀ n y, 0 ≤ ρ n y)
    (hρ1 : ∀ n, ∫ y, ρ n y ∂μ = 1)
    (hρ : ∀ n y, ε n < ‖y‖ → ρ n y = 0)
    (hΔ : ∀ᶠ n in atTop, ∀ x ∈ tsupport φ,
      0 ≤ Δ ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ n) x) :
    0 ≤ ∫ x, u x * Δ φ x ∂μ := by
  have hunif := LatticeProb.PegdenSmart.tendstoUniformlyOn_mollify (μ := μ) hU hu hε
    hρs hρc hρ0 hρ1 hρ hc hφU
  obtain ⟨δ, hδ, hδU⟩ := hc.exists_thickening_subset_open hU hφU
  have hsmall : ∀ᶠ n in atTop, ε n < δ / 2 :=
    hε.eventually (gt_mem_nhds (half_pos hδ))
  apply integral_mul_laplacian_nonneg_of_local_smooth_approximation (μ := μ) hφ hc hφ0 ?_ hunif
  filter_upwards [hsmall, hΔ] with n hn hnΔ
  refine ⟨thickening (δ / 2) (tsupport φ), isOpen_thickening,
    self_subset_thickening (half_pos hδ) (tsupport φ), ?_, hnΔ⟩
  apply (LatticeProb.PegdenSmart.contDiffOn_mollify (μ := μ) hU hu (hε0 n)
    (hρs n) (hρc n) (hρ n)).mono
  intro x hx y hy
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp hx
  apply hδU
  apply mem_thickening_iff.mpr
  refine ⟨z, hz, ?_⟩
  have hyx := mem_closedBall.mp hy
  linarith [dist_triangle y x z]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- A nonnegative ball-average increment has a nonnegative quadratic coefficient. -/
theorem nonneg_of_le_ballAverage_of_tendsto {f : E → ℝ} {a : E} {δ c L : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hmean : ∀ r : ℝ, 0 < r → r < δ → f a ≤ ⨍ y in ball a r, f y ∂μ)
    (hlim : Tendsto (fun r : ℝ => ((⨍ y in ball a r, f y ∂μ) - f a) / r ^ 2)
      (𝓝[>] 0) (𝓝 (c * L))) : 0 ≤ L := by
  have h : 0 ≤ c * L := ge_of_tendsto hlim ?_
  · exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using h) hc
  · filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    exact div_nonneg (sub_nonneg.mpr (hmean r hr.1 hr.2)) (sq_nonneg r)

/-- The integral of a linear function over a ball centred at the origin vanishes. -/
theorem integral_linear_ball_zero (L : E →L[ℝ] ℝ) (r : ℝ) :
    ∫ x in ball (0 : E) r, L x ∂μ = 0 := by
  have h : ∫ x in ball (0 : E) r, L (-x) ∂μ = ∫ x in ball (0 : E) r, L x ∂μ := by
    have hpre : (fun x : E => -x) ⁻¹' ball (0 : E) r = ball 0 r := by
      ext x
      simp
    simpa only [hpre] using (Measure.measurePreserving_neg μ).setIntegral_preimage_emb
      measurableEmbedding_neg L (ball 0 r)
  simp only [map_neg, integral_neg] at h
  linarith

/-- The integral of a linear function of the displacement from the centre of a ball vanishes. -/
theorem integral_linear_sub_center_ball (L : E →L[ℝ] ℝ) (a : E) (r : ℝ) :
    ∫ y in ball a r, L (y - a) ∂μ = 0 := by
  have hpre : (fun x : E => a + x) ⁻¹' ball a r = ball 0 r := by
    ext x
    simp [mem_ball, dist_eq_norm]
  have h := (measurePreserving_add_left μ a).setIntegral_preimage_emb
    (measurableEmbedding_addLeft a) (fun y => L (y - a)) (ball a r)
  rw [hpre] at h
  simp only [add_sub_cancel_left] at h
  rw [← h, integral_linear_ball_zero]


private theorem integral_comp_linearIsometryEquiv_ball (R : E ≃ₗᵢ[ℝ] E) (g : E → ℝ)
    (r : ℝ) : ∫ x in ball (0 : E) r, g (R x) ∂μ = ∫ x in ball (0 : E) r, g x ∂μ := by
  have hR : MeasurePreserving R μ μ := by
    rw [Measure.isAddLeftInvariant_eq_smul μ (volume : Measure E)]
    exact R.measurePreserving.smul_measure _
  have hpre : R ⁻¹' ball (0 : E) r = ball 0 r := by
    ext x
    simp only [mem_preimage, mem_ball, dist_zero_right, R.norm_map]
  simpa only [hpre] using hR.setIntegral_preimage_emb
    R.toMeasurableEquiv.measurableEmbedding g (ball 0 r)

/-- Orthogonal coordinate functions have zero mixed moment on a centred ball. -/
theorem integral_inner_mul_inner_ball_eq_zero (u v : E) (huv : ⟪u, v⟫_ℝ = 0) (r : ℝ) :
    ∫ x in ball (0 : E) r, ⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ ∂μ = 0 := by
  let R := (ℝ ∙ u).reflection
  have hu : R u = u :=
    Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self u)
  have hv : R v = -v := by
    dsimp [R]
    rw [Submodule.reflection_singleton_apply, huv]
    simp
  have h := integral_comp_linearIsometryEquiv_ball (μ := μ) R
    (fun x => ⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ) r
  have hinner (x : E) : ⟪u, R x⟫_ℝ * ⟪v, R x⟫_ℝ =
      -(⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ) := by
    have h1 := R.inner_map_map u x
    have h2 := R.inner_map_map v x
    rw [hu] at h1
    rw [hv, inner_neg_left] at h2
    have h2x : ⟪v, R x⟫_ℝ = -⟪v, x⟫_ℝ := by linarith
    rw [h1, h2x, mul_neg]
  simp_rw [hinner, integral_neg] at h
  linarith

/-- Vectors of equal norm have equal quadratic moments on a centred ball. -/
theorem integral_inner_sq_ball_eq (u v : E) (h : ‖u‖ = ‖v‖) (r : ℝ) :
    ∫ x in ball (0 : E) r, ⟪u, x⟫_ℝ ^ 2 ∂μ =
      ∫ x in ball (0 : E) r, ⟪v, x⟫_ℝ ^ 2 ∂μ := by
  let R := (ℝ ∙ (u - v))ᗮ.reflection
  have hu : R u = v := Submodule.reflection_sub h
  have hi := integral_comp_linearIsometryEquiv_ball (μ := μ) R
    (fun x => ⟪v, x⟫_ℝ ^ 2) r
  have hinner (x : E) : ⟪v, R x⟫_ℝ = ⟪u, x⟫_ℝ := by
    simpa only [hu] using R.inner_map_map u x
  simp_rw [hinner] at hi
  exact hi

/-- A unit coordinate has positive quadratic moment on a ball of positive radius. -/
theorem integral_inner_sq_ball_pos (u : E) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 < r) :
    0 < ∫ x in ball (0 : E) r, ⟪u, x⟫_ℝ ^ 2 ∂μ := by
  let f : E → ℝ := fun x => ⟪u, x⟫_ℝ ^ 2
  have hf : Continuous f := (continuous_const.inner continuous_id).pow 2
  have hfi : IntegrableOn f (ball (0 : E) r) μ :=
    hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) r) |>.mono_set ball_subset_closedBall
  apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _) hfi).2
  have hopen : IsOpen (Function.support f ∩ ball (0 : E) r) :=
    hf.isOpen_support.inter isOpen_ball
  apply hopen.measure_pos (μ := μ)
  use (r / 2) • u
  constructor
  · have hinner : ⟪u, (r / 2) • u⟫_ℝ = r / 2 := by
      simp [real_inner_smul_right, hu]
    simp [Function.mem_support, f, hinner, ne_of_gt (half_pos hr)]
  · simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, hu, mul_one,
      abs_of_pos (half_pos hr)]
    linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The second-order Taylor remainder of a smooth function is locally quadratic with
an arbitrarily small coefficient. -/
theorem exists_taylor_remainder_le {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ y : E, ‖y‖ ≤ r →
      |f (a + y) - f a - fderiv ℝ f a y - (1 / 2 : ℝ) *
        fderiv ℝ (fderiv ℝ f) a y y| ≤ ε * ‖y‖ ^ 2 := by
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hH : Continuous (fderiv ℝ (fderiv ℝ f)) := hDf.continuous_fderiv (by simp)
  obtain ⟨r, hr, hdist⟩ := (Metric.continuous_iff (f := fderiv ℝ (fderiv ℝ f)) |>.mp hH) a ε hε
  refine ⟨r / 2, half_pos hr, fun y hy => ?_⟩
  apply LatticeProb.taylor_remainder_le_of_hessian_oscillation (convex_closedBall a (r / 2))
    (fun z _ => hf.differentiable (by simp) z)
    (fun z _ => hDf.differentiable (by simp) z)
    (mem_closedBall_self (half_pos hr).le)
    (by simpa [mem_closedBall, dist_eq_norm] using hy) hε.le
  intro z hz
  have hz' : dist z a < r := lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hr)
  calc
    _ = dist (fderiv ℝ (fderiv ℝ f) z) (fderiv ℝ (fderiv ℝ f) a) := (dist_eq_norm (fderiv ℝ (fderiv ℝ f) z) (fderiv ℝ (fderiv ℝ f) a)).symm
    _ ≤ ε := (hdist z hz').le

/-- The integral of a quadratic form on a centred ball is its trace times a
coordinate quadratic moment. -/
theorem integral_bilinear_ball_eq_trace {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (i₀ : ι)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) :
    ∫ x in ball (0 : E) r, H x x ∂μ =
      (∫ x in ball (0 : E) r, ⟪b i₀, x⟫_ℝ ^ 2 ∂μ) * ∑ i, H (b i) (b i) := by
  classical
  let g : ι → ι → E → ℝ := fun i j x => ⟪b i, x⟫_ℝ * ⟪b j, x⟫_ℝ * H (b i) (b j)
  have hgi (i j : ι) : IntegrableOn (g i j) (ball (0 : E) r) μ := by
    apply (Continuous.continuousOn ?_).integrableOn_compact (isCompact_closedBall 0 r) |>.mono_set ball_subset_closedBall
    exact ((continuous_const.inner continuous_id).mul (continuous_const.inner continuous_id)).mul continuous_const
  have hexp (x : E) : H x x = ∑ i, ∑ j, g i j x := by
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul, Finset.mul_sum, g]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hg (i j : ι) : ∫ x in ball (0 : E) r, g i j x ∂μ =
      if i = j then (∫ x in ball (0 : E) r, ⟪b i₀, x⟫_ℝ ^ 2 ∂μ) * H (b i) (b j) else 0 := by
    simp only [g, integral_mul_const]
    split_ifs with hij
    · subst j
      simp_rw [← pow_two]
      rw [integral_inner_sq_ball_eq (μ := μ) (b i) (b i₀) (by simp) r]
    · rw [integral_inner_mul_inner_ball_eq_zero (μ := μ) (b i) (b j) (by
        simp [orthonormal_iff_ite.mp b.orthonormal, hij]) r, zero_mul]
  calc
    _ = ∫ x in ball (0 : E) r, ∑ i, ∑ j, g i j x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hexp
    _ = ∑ i, ∑ j, ∫ x in ball (0 : E) r, g i j x ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hgi i j)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hgi i j)]
    _ = _ := by simp [hg, Finset.mul_sum]

open scoped Pointwise
/-- Scaling the radius of a centred ball scales its quadratic moment by the appropriate power. -/
theorem integral_inner_sq_ball_scale (u : E) {r : ℝ} (hr : 0 < r) :
    ∫ x in ball (0 : E) r, ⟪u, x⟫_ℝ ^ 2 ∂μ =
      r ^ Module.finrank ℝ E * r ^ 2 * ∫ x in ball (0 : E) 1, ⟪u, x⟫_ℝ ^ 2 ∂μ := by
  have hs : r • ball (0 : E) 1 = ball 0 r := by
    rw [_root_.smul_ball hr.ne']
    simp [Real.norm_eq_abs, abs_of_pos hr]
  have h := Measure.setIntegral_comp_smul_of_pos μ (fun x => ⟪u, x⟫_ℝ ^ 2) (ball (0 : E) 1) hr
  rw [hs] at h
  simp only [real_inner_smul_right, mul_pow, integral_const_mul, smul_eq_mul] at h
  have hp : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp at h
  linarith

/-- Scaling the radius of a centred ball scales its Haar measure by the dimension power. -/
theorem measureReal_ball_scale {r : ℝ} (hr : 0 < r) :
    μ.real (ball (0 : E) r) = r ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) := by
  have hs : r • ball (0 : E) 1 = ball 0 r := by
    rw [_root_.smul_ball hr.ne']
    simp [Real.norm_eq_abs, abs_of_pos hr]
  have h := Measure.setIntegral_comp_smul_of_pos μ (fun _ : E => (1 : ℝ)) (ball (0 : E) 1) hr
  rw [hs] at h
  simp only [setIntegral_const, smul_eq_mul, mul_one] at h
  have hp : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp at h
  linarith
/-- A quadratic coordinate average on a centred ball scales as the square of the radius. -/
theorem average_inner_sq_ball_scale (u : E) {r : ℝ} (hr : 0 < r) :
    ⨍ x in ball (0 : E) r, ⟪u, x⟫_ℝ ^ 2 ∂μ =
      r ^ 2 * ⨍ x in ball (0 : E) 1, ⟪u, x⟫_ℝ ^ 2 ∂μ := by
  rw [setAverage_eq, setAverage_eq, measureReal_ball_scale (μ := μ) hr,
    integral_inner_sq_ball_scale (μ := μ) u hr]
  simp only [smul_eq_mul]
  have hp : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp

/-- The average of a quadratic form on a centred ball is its trace times a
coordinate quadratic moment. -/
theorem average_bilinear_ball_eq_trace {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (i₀ : ι)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) :
    ⨍ x in ball (0 : E) r, H x x ∂μ =
      (⨍ x in ball (0 : E) r, ⟪b i₀, x⟫_ℝ ^ 2 ∂μ) * ∑ i, H (b i) (b i) := by
  rw [setAverage_eq, setAverage_eq, integral_bilinear_ball_eq_trace b i₀ H r]
  simp only [smul_eq_mul, mul_assoc]

/-- A unit coordinate has positive quadratic average on a ball of positive radius. -/
theorem average_inner_sq_ball_pos (u : E) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 < r) :
    0 < ⨍ x in ball (0 : E) r, ⟪u, x⟫_ℝ ^ 2 ∂μ := by
  rw [setAverage_eq]
  have hm : 0 < μ.real (ball (0 : E) r) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne
  exact mul_pos (inv_pos.mpr hm) (integral_inner_sq_ball_pos u hu hr)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Translation moves a ball average to a ball centred at the origin. -/
theorem average_add_ball (f : E → ℝ) (a : E) (r : ℝ) :
    ⨍ x in ball (0 : E) r, f (a + x) ∂μ = ⨍ x in ball a r, f x ∂μ := by
  have hpre : (fun x : E => a + x) ⁻¹' ball a r = ball 0 r := by
    ext x
    simp [mem_ball, dist_eq_norm]
  have hm := (measurePreserving_add_left μ a).measure_preimage_emb
    (measurableEmbedding_addLeft a) (ball a r)
  have hi := (measurePreserving_add_left μ a).setIntegral_preimage_emb
    (measurableEmbedding_addLeft a) f (ball a r)
  rw [hpre] at hm hi
  rw [setAverage_eq, setAverage_eq, measureReal_def, measureReal_def, hm, hi]
/-- A linear function has zero average on a centred ball. -/
theorem average_linear_ball_zero (L : E →L[ℝ] ℝ) (r : ℝ) :
    ⨍ x in ball (0 : E) r, L x ∂μ = 0 := by
  rw [setAverage_eq, integral_linear_ball_zero]
  simp

/-- A pointwise Taylor remainder bound controls its ball average. -/
theorem average_taylor_remainder_le {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E) {ε r : ℝ} (hε : 0 ≤ ε)
    (hr : 0 < r)
    (ht : ∀ x : E, ‖x‖ ≤ r →
      |f (a + x) - f a - fderiv ℝ f a x - (1 / 2 : ℝ) *
        fderiv ℝ (fderiv ℝ f) a x x| ≤ ε * ‖x‖ ^ 2) :
    (⨍ x in ball (0 : E) r, f (a + x) ∂μ) - f a -
      (1 / 2 : ℝ) * ⨍ x in ball (0 : E) r, fderiv ℝ (fderiv ℝ f) a x x ∂μ ≤ ε * r ^ 2 := by
  let L := fderiv ℝ f a
  let H := fderiv ℝ (fderiv ℝ f) a
  let R : E → ℝ := fun x => f (a + x) - f a - L x - (1 / 2 : ℝ) * H x x
  have hcont (g : E → ℝ) (hg : Continuous g) : IntegrableOn g (ball (0 : E) r) μ :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hF : Continuous (fun x => f (a + x)) := hf.continuous.comp (continuous_const.add continuous_id)
  have hH : Continuous (fun x => H x x) := (H.continuous.clm_apply continuous_id)
  have hR : IntegrableOn R (ball (0 : E) r) μ :=
    hcont _ (((hF.sub continuous_const).sub L.continuous).sub (continuous_const.mul hH))
  have hbound (x : E) (hx : x ∈ ball (0 : E) r) : R x ≤ ε * r ^ 2 := by
    have hx' : ‖x‖ ≤ r := (mem_ball_zero_iff.mp hx).le
    have h := le_trans (le_abs_self (R x)) (ht x hx')
    exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) hx' 2) hε)
  have hI := setIntegral_mono_on hR (integrableOn_const (measure_ball_lt_top.ne)) measurableSet_ball hbound
  have hA : (⨍ x in ball (0 : E) r, R x ∂μ) ≤ ε * r ^ 2 := by
    rw [setAverage_eq]
    have hm : 0 < μ.real (ball (0 : E) r) :=
      ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne
    have hh := mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hm.le)
    simpa [setIntegral_const, smul_eq_mul, hm.ne', mul_assoc] using hh
  have hm0 : μ (ball (0 : E) r) ≠ 0 := (measure_ball_pos μ 0 hr).ne'
  have havg : (⨍ x in ball (0 : E) r, R x ∂μ) =
      (⨍ x in ball (0 : E) r, f (a + x) ∂μ) - f a -
        (1 / 2 : ℝ) * ⨍ x in ball (0 : E) r, H x x ∂μ := by
    change (⨍ x in ball (0 : E) r,
      (((fun x : E => f (a + x)) - (fun _ : E => f a)) - (L : E → ℝ) -
        (fun x : E => (1 / 2 : ℝ) * H x x)) x ∂μ) = _
    have hc : IntegrableOn (fun _ : E => f a) (ball 0 r) μ :=
      integrableOn_const measure_ball_lt_top.ne
    have hL : IntegrableOn L (ball 0 r) μ := hcont _ L.continuous
    have hQ : IntegrableOn (fun x => (1 / 2 : ℝ) * H x x) (ball 0 r) μ :=
      (hcont _ hH).const_mul _
    rw [setAverage_sub (((hcont _ hF).sub hc).sub hL) hQ,
      setAverage_sub ((hcont _ hF).sub hc) hL,
      setAverage_sub (hcont _ hF) hc,
      setAverage_const hm0 measure_ball_lt_top.ne, average_linear_ball_zero, average_const_mul]
    ring
  rw [havg] at hA
  exact hA

/-- In positive dimension, a smooth function with the local ball sub-mean property has
a nonnegative Laplacian. -/
theorem laplacian_nonneg_of_le_ballAverage_of_nontrivial [Nontrivial E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E) {δ : ℝ} (hδ : 0 < δ)
    (hmean : ∀ r : ℝ, 0 < r → r < δ → f a ≤ ⨍ y in ball a r, f y ∂μ) :
    0 ≤ Δ f a := by
  classical
  by_contra hn
  have hn' : Δ f a < 0 := lt_of_not_ge hn
  let b := stdOrthonormalBasis ℝ E
  let i₀ : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let c : ℝ := ⨍ x in ball (0 : E) 1, ⟪b i₀, x⟫_ℝ ^ 2 ∂μ
  have hc : 0 < c := average_inner_sq_ball_pos (μ := μ) (b i₀) (by simp [b]) zero_lt_one
  let ε := -(c * Δ f a) / 4
  have hε : 0 < ε := div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hc hn')) (by norm_num)
  obtain ⟨s, hs, ht⟩ := exists_taylor_remainder_le hf a hε
  let r := min s δ / 2
  have hr : 0 < r := half_pos (lt_min hs hδ)
  have hrs : r ≤ s := (half_le_self (le_of_lt (lt_min hs hδ))).trans (min_le_left _ _)
  have hrδ : r < δ := lt_of_lt_of_le (half_lt_self (lt_min hs hδ)) (min_le_right _ _)
  have hbound := average_taylor_remainder_le (μ := μ) hf a hε.le hr
    (fun x hx => ht x (le_trans hx hrs))
  have hΔ : Δ f a = ∑ i, fderiv ℝ (fderiv ℝ f) a (b i) (b i) := by
    rw [laplacian_eq_sum_fderiv hf]
    apply Finset.sum_congr rfl
    intro i _
    have hd : DifferentiableAt ℝ (fderiv ℝ f) a :=
      (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) a
    rw [fderiv_clm_apply hd (differentiableAt_const (b i))]
    simp [b]
  have hq : (⨍ x in ball (0 : E) r, fderiv ℝ (fderiv ℝ f) a x x ∂μ) = r ^ 2 * c * Δ f a := by
    rw [average_bilinear_ball_eq_trace b i₀, average_inner_sq_ball_scale _ hr, ← hΔ]
  have hm : f a ≤ ⨍ x in ball (0 : E) r, f (a + x) ∂μ := by
    rw [average_add_ball]
    exact hmean r hr hrδ
  rw [hq] at hbound
  have hbad : (1 / 2 : ℝ) * (r ^ 2 * c * Δ f a) + ε * r ^ 2 < 0 := by
    dsimp [ε]
    have hnprod : c * Δ f a < 0 := mul_neg_of_pos_of_neg hc hn'
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have := mul_neg_of_pos_of_neg hr2 hnprod
    nlinarith
  linarith

/-- A smooth function satisfying the local ball sub-mean property has nonnegative Laplacian. -/
theorem laplacian_nonneg_of_le_ballAverage {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E) {δ : ℝ} (hδ : 0 < δ)
    (hmean : ∀ r : ℝ, 0 < r → r < δ → f a ≤ ⨍ y in ball a r, f y ∂μ) :
    0 ≤ Δ f a := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hconst : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
    rw [hconst]
    simp
  · let _ := hE
    exact laplacian_nonneg_of_le_ballAverage_of_nontrivial (μ := μ) hf a hδ hmean

/-- A locally smooth function satisfying the ball sub-mean property has nonnegative
Laplacian at each point of its domain. -/
theorem laplacian_nonneg_of_contDiffOn_of_le_ballAverage {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {a : E} (ha : a ∈ U)
    (hmean : ∀ r : ℝ, 0 < r → ball a r ⊆ U → f a ≤ ⨍ y in ball a r, f y ∂μ) :
    0 ≤ Δ f a := by
  obtain ⟨g, V, hV, haV, hg, heq⟩ :=
    exists_smooth_extension_near_compact isCompact_singleton hU (singleton_subset_iff.mpr ha) hf
  have haV' : a ∈ V := haV (mem_singleton a)
  obtain ⟨δ, hδ, hδVU⟩ := Metric.isOpen_iff.mp (hV.inter hU) a ⟨haV', ha⟩
  have hδV : ball a δ ⊆ V := hδVU.trans inter_subset_left
  have hδU : ball a δ ⊆ U := hδVU.trans inter_subset_right
  have hgmean : ∀ r : ℝ, 0 < r → r < δ → g a ≤ ⨍ y in ball a r, g y ∂μ := by
    intro r hr hrδ
    have hrV : ball a r ⊆ V := (ball_subset_ball hrδ.le).trans hδV
    have hrU : ball a r ⊆ U := (ball_subset_ball hrδ.le).trans hδU
    have havg : (⨍ y in ball a r, g y ∂μ) = ⨍ y in ball a r, f y ∂μ := by
      apply setAverage_congr_fun measurableSet_ball
      exact Filter.Eventually.of_forall fun y hy => heq (hrV hy)
    rw [heq haV', havg]
    exact hmean r hr hrU
  have h := laplacian_nonneg_of_le_ballAverage (μ := μ) hg a hδ hgmean
  have hev : g =ᶠ[𝓝 a] f := by
    filter_upwards [hV.mem_nhds haV'] with y hy
    exact heq hy
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds] at h
  exact h

end LatticeProb.Ishii
