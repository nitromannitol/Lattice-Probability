import LatticeProb.Analysis.WeakLaplaceMollify
import LatticeProb.Analysis.LaplacianCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Bounds for distributional Laplacians

A two-sided bound on the distributional Laplacian bounds the Laplacian of its
local mollifications.
-/

open MeasureTheory Metric Filter Topology Set
open scoped InnerProductSpace ContDiff Convolution
open Laplacian

namespace LatticeProb.PegdenSmart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A smooth cutoff gives a smooth approximation from above to the absolute
value of a compactly supported function. -/
theorem exists_smooth_abs_majorant {φ χ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x ∈ Function.support φ, χ x = 1)
    (hχle : ∀ x, χ x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : E → ℝ, ContDiff ℝ ∞ q ∧ HasCompactSupport q ∧
      tsupport q ⊆ tsupport χ ∧ ∀ x, |φ x| ≤ q x ∧ q x ≤ |φ x| + ε * χ x := by
  let q : E → ℝ := fun x => χ x * Real.sqrt (φ x ^ 2 + ε ^ 2)
  have hpos : ∀ x, 0 < φ x ^ 2 + ε ^ 2 := fun x => by positivity
  have hq : ContDiff ℝ ∞ q := hχ.mul ((hφ.pow 2 |>.add contDiff_const).sqrt
    fun x => (hpos x).ne')
  refine ⟨q, hq, hχc.mul_right, tsupport_mul_subset_left, fun x => ?_⟩
  have hs : 0 ≤ Real.sqrt (φ x ^ 2 + ε ^ 2) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (φ x ^ 2 + ε ^ 2) ^ 2 = φ x ^ 2 + ε ^ 2 :=
    Real.sq_sqrt (hpos x).le
  have ha : 0 ≤ |φ x| := abs_nonneg _
  have ha2 : |φ x| ^ 2 = φ x ^ 2 := sq_abs _
  have hlow : |φ x| ≤ Real.sqrt (φ x ^ 2 + ε ^ 2) := by nlinarith
  have hhigh : Real.sqrt (φ x ^ 2 + ε ^ 2) ≤ |φ x| + ε := by nlinarith
  constructor
  · by_cases hx : x ∈ Function.support φ
    · simp only [q, hχ1 x hx, one_mul]; exact hlow
    · have hz : φ x = 0 := Function.notMem_support.mp hx
      simpa [q, hz] using mul_nonneg (hχ0 x) (Real.sqrt_nonneg (ε ^ 2))
  · calc
      q x ≤ χ x * (|φ x| + ε) := mul_le_mul_of_nonneg_left hhigh (hχ0 x)
      _ ≤ |φ x| + ε * χ x := by nlinarith [hχle x]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A compact set contained in an open set admits a smooth compactly
supported cutoff that equals one on it. -/
theorem exists_smooth_cutoff {U C : Set E} (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x ∈ C, χ x = 1) ∧ (∀ x, χ x ≤ 1) := by
  obtain ⟨r, hr⟩ := hC.isBounded.subset_ball (0 : E)
  have hV : IsOpen (U ∩ ball (0 : E) r) := hU.inter isOpen_ball
  have hCV : C ⊆ U ∩ ball (0 : E) r := subset_inter hCU hr
  obtain ⟨V, hVo, hCV', hVsub⟩ := hC.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hCV)
  obtain ⟨χ, hχ, hχrange, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVo hC.isClosed hCV'
  have hχts : tsupport χ = closure V := by rw [tsupport, hχsupp]
  have hχc : HasCompactSupport χ := by
    rw [HasCompactSupport, hχts]
    exact (isCompact_closedBall (0 : E) r).of_isClosed_subset isClosed_closure
      (hVsub.trans (inter_subset_right.trans ball_subset_closedBall))
  exact ⟨χ, hχ, hχc, hχts ▸ hVsub.trans inter_subset_left,
    fun x => (hχrange ⟨x, rfl⟩).1, fun x hx => (hχone x).1 hx,
    fun x => (hχrange ⟨x, rfl⟩).2⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- A compactly supported continuous function can be uniformly approximated
by smooth functions supported in a fixed compact subset of an open set. -/
theorem exists_smooth_uniform_approx {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) :
    ∃ C : Set E, IsCompact C ∧ C ⊆ U ∧ ∀ ε : ℝ, 0 < ε →
      ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ C ∧
        ∀ x, |g x - f x| ≤ ε := by
  obtain ⟨χ, hχ, hχc, hχU, hχ0, hχ1, hχle⟩ :=
    exists_smooth_cutoff hU hfc.isCompact hfU
  refine ⟨tsupport χ, hχc.isCompact, hχU, fun ε hε => ?_⟩
  have hfu : UniformContinuous f :=
    hf.uniformContinuous_of_tendsto_cocompact hfc.is_zero_at_infty
  obtain ⟨g, hg, hga⟩ := hfu.exists_contDiff_dist_le hε
  refine ⟨fun x => χ x * g x, hχ.mul hg, hχc.mul_right, tsupport_mul_subset_left, fun x => ?_⟩
  have hχf : χ x * f x = f x := by
    by_cases hx : x ∈ tsupport f
    · rw [hχ1 x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hχabs : |χ x| ≤ 1 := abs_le.mpr ⟨by linarith [hχ0 x], hχle x⟩
  have hgabs : |g x - f x| < ε := by simpa [Real.dist_eq] using hga x
  calc
    |χ x * g x - f x| = |χ x| * |g x - f x| := by
      have heq : χ x * g x - f x = χ x * (g x - f x) := by nlinarith [hχf]
      rw [heq, abs_mul]
    _ ≤ 1 * |g x - f x| := mul_le_mul_of_nonneg_right hχabs (abs_nonneg _)
    _ ≤ ε := by simpa using hgabs.le

/-- The distributional Laplacian pairing is integrable for a test function
supported inside the domain of continuity. -/
theorem integrable_mul_laplacian {U : Set E} {u φ : E → ℝ}
    (hu : ContinuousOn u U) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun x => u x * Δ φ x) μ := by
  have hΔ : Continuous (Δ φ) :=
    LatticeProb.LaplacianCalculus.continuous_laplacian_of_contDiff (hφ.of_le (by simp))
  have hint : IntegrableOn (fun x => u x * Δ φ x) (tsupport φ) μ :=
    ((hu.mono hφU).mul hΔ.continuousOn).integrableOn_compact hφc.isCompact
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hint
  intro x hx
  by_contra hxt
  exact hx (by simp [LatticeProb.LaplacianCalculus.laplacian_eq_zero_off_tsupport hxt])

/-- The two-sided bound for nonnegative tests extends to all smooth tests
with the sharp integral bound by their absolute value. -/
theorem abs_integral_mul_laplacian_le {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContinuousOn u U) {K : ℝ} (hK : 0 ≤ K)
    (hle : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x) → |∫ x, u x * Δ φ x ∂μ| ≤ K * ∫ x, φ x ∂μ)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    |∫ x, u x * Δ φ x ∂μ| ≤ K * ∫ x, |φ x| ∂μ := by
  obtain ⟨χ, hχ, hχc, hχU, hχ0, hχ1, hχle⟩ :=
    exists_smooth_cutoff hU hφc.isCompact hφU
  have hχi : Integrable χ μ := hχ.continuous.integrable_of_hasCompactSupport hχc
  have hφi : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hTi : Integrable (fun x => u x * Δ φ x) μ :=
    integrable_mul_laplacian hu hφ hφc hφU
  have hχint : 0 ≤ ∫ x, χ x ∂μ := integral_nonneg hχ0
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  let ε := δ / (K * (∫ x, χ x ∂μ) + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨q, hq, hqc, hqχ, hqbound⟩ :=
    exists_smooth_abs_majorant hφ hχ hχc hχ0
      (fun x hx => hχ1 x (subset_tsupport φ hx)) hχle hε
  have hqU : tsupport q ⊆ U := hqχ.trans hχU
  have hqi : Integrable q μ := hq.continuous.integrable_of_hasCompactSupport hqc
  have hTqi : Integrable (fun x => u x * Δ q x) μ :=
    integrable_mul_laplacian hu hq hqc hqU
  have hplusU : tsupport (q + φ) ⊆ U := (tsupport_add _ _).trans (union_subset hqU hφU)
  have hminusU : tsupport (q - φ) ⊆ U := (tsupport_sub _ _).trans (union_subset hqU hφU)
  have hplus0 : ∀ x, 0 ≤ (q + φ) x := fun x => by
    have h := (hqbound x).1
    have h' := neg_abs_le (φ x)
    dsimp
    linarith
  have hminus0 : ∀ x, 0 ≤ (q - φ) x := fun x => by
    have h := (hqbound x).1
    have h' := le_abs_self (φ x)
    dsimp
    linarith
  have hp := hle (q + φ) (hq.add hφ) (hqc.add hφc) hplusU hplus0
  have hm := hle (q - φ) (hq.sub hφ) (hqc.sub hφc) hminusU hminus0
  have eplus : (∫ x, u x * Δ (q + φ) x ∂μ) =
      (∫ x, u x * Δ q x ∂μ) + ∫ x, u x * Δ φ x ∂μ := by
    rw [← integral_add hTqi hTi]
    congr 1; funext x
    rw [(hq.of_le (by simp)).contDiffAt.laplacian_add (hφ.of_le (by simp)).contDiffAt]
    ring
  have eminus : (∫ x, u x * Δ (q - φ) x ∂μ) =
      (∫ x, u x * Δ q x ∂μ) - ∫ x, u x * Δ φ x ∂μ := by
    rw [← integral_sub hTqi hTi]
    congr 1; funext x
    rw [(hq.of_le (by simp)).contDiffAt.laplacian_sub (hφ.of_le (by simp)).contDiffAt]
    ring
  simp only [Pi.add_apply] at hp
  simp only [Pi.sub_apply] at hm
  rw [eplus, integral_add hqi hφi] at hp
  rw [eminus, integral_sub hqi hφi] at hm
  have hmain : |∫ x, u x * Δ φ x ∂μ| ≤ K * ∫ x, q x ∂μ := by
    rw [abs_le] at hp hm ⊢
    constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]
  have hqint : (∫ x, q x ∂μ) ≤ (∫ x, |φ x| ∂μ) + ε * ∫ x, χ x ∂μ := by
    calc
      (∫ x, q x ∂μ) ≤ ∫ x, (|φ x| + ε * χ x) ∂μ :=
        integral_mono hqi (hφi.abs.add (hχi.const_mul ε)) fun x => (hqbound x).2
      _ = _ := by rw [integral_add hφi.abs (hχi.const_mul ε), integral_const_mul]
  have herr : K * (ε * ∫ x, χ x ∂μ) ≤ δ := by
    have hden : 0 < K * (∫ x, χ x ∂μ) + 1 := by positivity
    have heq : ε * (K * (∫ x, χ x ∂μ) + 1) = δ := by
      dsimp [ε]
      exact div_mul_cancel₀ δ hden.ne'
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hqint hK]

/-- A nonnegative unit-mass mollifier turns a two-sided distributional bound
into a pointwise bound on the mollified Laplacian. -/
theorem abs_laplacian_mollify_le_of_two_sided {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContinuousOn u U) {K : ℝ}
    (hle : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x) → |∫ x, u x * Δ φ x ∂μ| ≤ K * ∫ x, φ x ∂μ)
    {ρ : E → ℝ} {ε : ℝ} (hε : 0 < ε) (hρs : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρ : ∀ y, ε < ‖y‖ → ρ y = 0)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) {x₀ : E}
    (hx₀ : closedBall x₀ ε ⊆ U) :
    |Δ ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) x₀| ≤ K := by
  obtain ⟨η, hη, g, hg, hgu, hloc⟩ := exists_local_conv (μ := μ) hU hu hε hρ hx₀
  have hev : ((U.indicator u) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) =ᶠ[𝓝 x₀]
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] ρ) := by
    filter_upwards [ball_mem_nhds x₀ hη] with x hx using hloc x hx
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds,
    laplacian_convolution hg.locallyIntegrable hρs hρc]
  have hψ : ContDiff ℝ ∞ (fun t => ρ (x₀ - t)) := hρs.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun t => ρ (x₀ - t)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x₀)
  have hψU : tsupport (fun t => ρ (x₀ - t)) ⊆ U := by
    refine (closure_minimal (fun t ht => ?_) isClosed_closedBall).trans hx₀
    by_contra hnot
    rw [mem_closedBall, not_le, dist_eq_norm'] at hnot
    exact ht (hρ _ hnot)
  have h := hle _ hψ hψc hψU (fun t => hρ0 (x₀ - t))
  simp only [laplacian_comp_sub_left hρs x₀] at h
  rw [integral_sub_left_eq_self ρ μ x₀, hρ1, mul_one] at h
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  have h1 : ∫ t, g t * Δ ρ (x₀ - t) ∂μ = ∫ t, u t * Δ ρ (x₀ - t) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ closedBall x₀ ε
    · simp only [hgu ht]
    · have ht' : ε < ‖x₀ - t‖ := by
        rw [mem_closedBall, not_le, dist_eq_norm'] at ht
        exact ht
      dsimp only
      rw [laplacian_eq_zero_of_eq_zero hρ ht', mul_zero, mul_zero]
  rw [h1]
  exact h

end LatticeProb.PegdenSmart
