import LatticeProb.Analysis.WeakLaplaceMollify
import LatticeProb.Analysis.LaplacianCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Bounded density of the distributional Laplacian

A continuous function whose distributional Laplacian has a two-sided bound
has a measurable weak Laplacian with the same pointwise bound.
-/

open MeasureTheory Metric Filter Topology Set
open scoped InnerProductSpace ContDiff CompactlySupported NNReal ENNReal
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

omit [MeasurableSpace E] [BorelSpace E] in
/-- Smooth compactly supported test functions on an open set, viewed as a
subspace of real-valued functions on the ambient space. -/
def smoothTestSpace (U : Set E) : Submodule ℝ (E → ℝ) where
  carrier := {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U}
  zero_mem' := by
    exact ⟨contDiff_const, by simp [HasCompactSupport], by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
      (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_, ?_⟩
    · exact hf.2.1.smul_left
    · exact (tsupport_smul_subset_right (fun _ => c) f).trans hf.2.2

omit [FiniteDimensional ℝ E] in
/-- Each test function is integrable. -/
theorem smoothTestSpace.integrable {U : Set E} (φ : smoothTestSpace U) :
    Integrable (φ : E → ℝ) μ := φ.2.1.continuous.integrable_of_hasCompactSupport φ.2.2.1

/-- The canonical map from test functions to their `L¹` classes. -/
noncomputable def smoothTestSpace.toL1 (U : Set E) : smoothTestSpace U →ₗ[ℝ] Lp ℝ 1 μ where
  toFun φ := (memLp_one_iff_integrable.mpr (smoothTestSpace.integrable (μ := μ) φ)).toLp (φ : E → ℝ)
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    rfl
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]
    rfl

omit [FiniteDimensional ℝ E] in
/-- The norm of a test function in `L¹` is the integral of its absolute value. -/
theorem smoothTestSpace.norm_toL1 {U : Set E} (φ : smoothTestSpace U) :
    ‖smoothTestSpace.toL1 (μ := μ) U φ‖ = ∫ x, |(φ : E → ℝ) x| ∂μ := by
  have hi := smoothTestSpace.integrable (μ := μ) φ
  change ‖(memLp_one_iff_integrable.mpr hi).toLp (φ : E → ℝ)‖ = _
  rw [Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  simp only [Real.norm_eq_abs]
  exact hi.aestronglyMeasurable

/-- The distributional Laplacian pairing as a linear functional on tests. -/
noncomputable def smoothTestSpace.laplacianPairing {U : Set E} {u : E → ℝ}
    (hu : ContinuousOn u U) : smoothTestSpace U →ₗ[ℝ] ℝ where
  toFun φ := ∫ x, u x * Δ (φ : E → ℝ) x ∂μ
  map_add' φ ψ := by
    have hiφ := integrable_mul_laplacian (μ := μ) hu φ.2.1 φ.2.2.1 φ.2.2.2
    have hiψ := integrable_mul_laplacian (μ := μ) hu ψ.2.1 ψ.2.2.1 ψ.2.2.2
    rw [← integral_add hiφ hiψ]
    congr 1; funext x
    change u x * Δ ((φ : E → ℝ) + (ψ : E → ℝ)) x = _
    rw [(φ.2.1.of_le (by simp)).contDiffAt.laplacian_add
      (ψ.2.1.of_le (by simp)).contDiffAt]
    ring
  map_smul' c φ := by
    simp only [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1; funext x
    change u x * Δ (c • (φ : E → ℝ)) x = _
    rw [InnerProductSpace.laplacian_smul c (φ.2.1.of_le (by simp)).contDiffAt]
    simp only [smul_eq_mul]
    ring

/-- A bounded distributional Laplacian extends to a bounded linear functional
on `L¹`, preserving its bound. -/
theorem exists_l1_extension_of_two_sided {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContinuousOn u U) {K : ℝ} (hK : 0 ≤ K)
    (hle : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x) → |∫ x, u x * Δ φ x ∂μ| ≤ K * ∫ x, φ x ∂μ) :
    ∃ F : StrongDual ℝ (Lp ℝ 1 μ), ‖F‖ ≤ K ∧
      ∀ φ : smoothTestSpace U, F (smoothTestSpace.toL1 (μ := μ) U φ) =
        ∫ x, u x * Δ (φ : E → ℝ) x ∂μ := by
  let J := smoothTestSpace.toL1 (μ := μ) U
  let T := smoothTestSpace.laplacianPairing (μ := μ) hu
  have hbound : ∀ φ, ‖T φ‖ ≤ K * ‖J φ‖ := by
    intro φ
    rw [smoothTestSpace.norm_toL1]
    exact abs_integral_mul_laplacian_le hU hu hK hle φ.2.1 φ.2.2.1 φ.2.2.2
  have hker : LinearMap.ker J ≤ LinearMap.ker T := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have h := hbound φ
    rw [hφ, norm_zero, mul_zero] at h
    exact norm_le_zero_iff.mp h
  let G : LinearMap.range J →ₗ[ℝ] ℝ :=
    (LinearMap.ker J).liftQ T hker |>.comp J.quotKerEquivRange.symm.toLinearMap
  have hG (φ : smoothTestSpace U) : G ⟨J φ, LinearMap.mem_range_self J φ⟩ = T φ := by
    simp [G, LinearMap.quotKerEquivRange_symm_apply_image]
  have hGb : ∀ z : LinearMap.range J, ‖G z‖ ≤ K * ‖z‖ := by
    rintro ⟨_, ⟨φ, rfl⟩⟩
    simpa [hG] using hbound φ
  let L : StrongDual ℝ (LinearMap.range J) := G.mkContinuous K hGb
  have hL : ‖L‖ ≤ K := L.opNorm_le_bound hK hGb
  obtain ⟨F, hF, hFnorm⟩ := exists_extension_norm_eq (LinearMap.range J) L
  refine ⟨F, hFnorm ▸ hL, fun φ => ?_⟩
  exact (hF ⟨J φ, LinearMap.mem_range_self J φ⟩).trans (hG φ)

/-- The canonical inclusion of compactly supported continuous functions in `L¹`. -/
noncomputable def compactlySupportedToL1 : C_c(E, ℝ) →ₗ[ℝ] Lp ℝ 1 μ where
  toFun f := (memLp_one_iff_integrable.mpr f.integrable).toLp f
  map_add' f g := by
    rw [← MemLp.toLp_add]
    rfl
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The `L¹` norm of a compactly supported continuous function. -/
theorem norm_compactlySupportedToL1 (f : C_c(E, ℝ)) :
    ‖compactlySupportedToL1 (μ := μ) f‖ = ∫ x, |f x| ∂μ := by
  change ‖(memLp_one_iff_integrable.mpr f.integrable).toLp f‖ = _
  rw [Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm f.integrable.aestronglyMeasurable]
  · simp only [Real.norm_eq_abs]
  · exact f.integrable.aestronglyMeasurable

/-- Adding `K` times integration to a norm-`K` functional makes it positive. -/
noncomputable def l1PositiveMap (F : StrongDual ℝ (Lp ℝ 1 μ)) (K : ℝ)
    (hF : ‖F‖ ≤ K) : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    (F.toLinearMap.comp (compactlySupportedToL1 (μ := μ)) +
      K • (CompactlySupportedContinuousMap.integralPositiveLinearMap μ).toLinearMap)
    (by
      intro f hf
      have hb := F.le_opNorm (compactlySupportedToL1 (μ := μ) f)
      have hnorm : ‖compactlySupportedToL1 (μ := μ) f‖ = ∫ x, f x ∂μ := by
        rw [norm_compactlySupportedToL1]
        congr 1; funext x
        exact abs_of_nonneg (hf x)
      rw [hnorm, Real.norm_eq_abs] at hb
      have hi : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hf
      have hb' : |F (compactlySupportedToL1 (μ := μ) f)| ≤ K * ∫ x, f x ∂μ :=
        hb.trans (mul_le_mul_of_nonneg_right hF hi)
      change 0 ≤ F (compactlySupportedToL1 (μ := μ) f) + K * ∫ x, f x ∂μ
      linarith [(abs_le.mp hb').1])

/-- A bounded `L¹` functional gives a positive measure dominated by `2K` times
the reference measure. -/
theorem exists_dominated_measure_of_l1 (F : StrongDual ℝ (Lp ℝ 1 μ))
    {K : ℝ} (hK : 0 ≤ K) (hF : ‖F‖ ≤ K) :
    ∃ ν : Measure E, ν.Regular ∧ ν ≤ (Real.toNNReal (2 * K)) • μ ∧
      ∀ f : C_c(E, ℝ), ∫ x, f x ∂ν =
        F (compactlySupportedToL1 (μ := μ) f) + K * ∫ x, f x ∂μ := by
  let P := l1PositiveMap (μ := μ) F K hF
  have hneg : ‖-F‖ ≤ K := by simpa using hF
  let Q := l1PositiveMap (μ := μ) (-F) K hneg
  let ν := RealRMK.rieszMeasure P
  let ξ := RealRMK.rieszMeasure Q
  let c : ℝ≥0 := Real.toNNReal (2 * K)
  have hc : (c : ℝ) = 2 * K := Real.coe_toNNReal _ (by positivity)
  have : ν.Regular := by dsimp [ν]; infer_instance
  have : ξ.Regular := by dsimp [ξ]; infer_instance
  have : IsFiniteMeasureOnCompacts (ν + ξ) := ⟨fun _ h => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨h.measure_lt_top, h.measure_lt_top⟩⟩
  have hsum : ν + ξ = c • μ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_add_measure f.integrable f.integrable, integral_smul_nnreal_measure]
    change (∫ x, f x ∂(RealRMK.rieszMeasure P)) +
      (∫ x, f x ∂(RealRMK.rieszMeasure Q)) = c • ∫ x, f x ∂μ
    rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    change F (compactlySupportedToL1 (μ := μ) f) + K * (∫ x, f x ∂μ) +
      ((-F) (compactlySupportedToL1 (μ := μ) f) + K * (∫ x, f x ∂μ)) =
      (c : ℝ) * ∫ x, f x ∂μ
    rw [hc]
    simp only [neg_apply]
    ring
  refine ⟨ν, inferInstance, ?_, fun f => ?_⟩
  · calc ν ≤ ν + ξ := Measure.le_add_right le_rfl
      _ = (Real.toNNReal (2 * K)) • μ := hsum
  · change (∫ x, f x ∂(RealRMK.rieszMeasure P)) = _
    rw [RealRMK.integral_rieszMeasure]
    rfl

/-- A bounded functional on `L¹` is represented on compactly supported
continuous functions by a pointwise bounded measurable function. -/
theorem exists_bounded_density_of_l1 (F : StrongDual ℝ (Lp ℝ 1 μ))
    {K : ℝ} (hK : 0 ≤ K) (hF : ‖F‖ ≤ K) :
    ∃ s : E → ℝ, Measurable s ∧ (∀ x, |s x| ≤ K) ∧
      ∀ f : C_c(E, ℝ), F (compactlySupportedToL1 (μ := μ) f) = ∫ x, s x * f x ∂μ := by
  obtain ⟨ν, hνreg, hνle, hνint⟩ := exists_dominated_measure_of_l1 (μ := μ) F hK hF
  let c : ℝ≥0 := Real.toNNReal (2 * K)
  have hc : (c : ℝ) = 2 * K := Real.coe_toNNReal _ (by positivity)
  have hνle' : ν ≤ (c : ℝ≥0∞) • μ := hνle
  have hνac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hνle'
  have : SigmaFinite ν := Measure.sigmaFinite_of_le (c • μ) hνle
  have hrn : μ.withDensity (ν.rnDeriv μ) = ν := Measure.withDensity_rnDeriv_eq ν μ hνac
  have hrtop : ∀ᵐ x ∂μ, ν.rnDeriv μ x < (⊤ : ℝ≥0∞) := Measure.rnDeriv_lt_top ν μ
  have hrle : ∀ᵐ x ∂μ, ν.rnDeriv μ x ≤ (c : ℝ≥0∞) := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (ν.measurable_rnDeriv μ) fun A _ _ => ?_
    calc
      (∫⁻ x in A, ν.rnDeriv μ x ∂μ) ≤ ν A := Measure.setLIntegral_rnDeriv_le A
      _ ≤ ((c : ℝ≥0∞) • μ) A := hνle' A
      _ = ∫⁻ _ in A, (c : ℝ≥0∞) ∂μ := by simp [Measure.smul_apply]
  let t : E → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have htm : Measurable t := (ν.measurable_rnDeriv μ).ennreal_toReal
  have htb : ∀ᵐ x ∂μ, 0 ≤ t x ∧ t x ≤ 2 * K := by
    filter_upwards [hrle] with x hx
    constructor
    · exact ENNReal.toReal_nonneg
    · have h := ENNReal.toReal_mono (by simp : (c : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) hx
      simpa [t, hc] using h
  let s : E → ℝ := fun x => max (-K) (min K (t x - K))
  have hsm : Measurable s := (measurable_const.max (measurable_const.min (htm.sub_const K)))
  have hsb : ∀ x, |s x| ≤ K := by
    intro x
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hst : ∀ᵐ x ∂μ, s x = t x - K := by
    filter_upwards [htb] with x hx
    change max (-K) (min K (t x - K)) = t x - K
    rw [min_eq_right (by linarith [hx.2]), max_eq_right (by linarith [hx.1])]
  refine ⟨s, hsm, hsb, fun f => ?_⟩
  have hti : Integrable (fun x => t x * f x) μ :=
    f.integrable.bdd_mul htm.aestronglyMeasurable (htb.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact hx.2)
  have htd : ∫ x, f x ∂ν = ∫ x, t x * f x ∂μ := by
    rw [← hrn, integral_withDensity_eq_integral_toReal_smul (ν.measurable_rnDeriv μ) hrtop]
    rfl
  have heq : (∫ x, s x * f x ∂μ) = (∫ x, t x * f x ∂μ) - K * ∫ x, f x ∂μ := by
    rw [← integral_const_mul K, ← integral_sub hti (f.integrable.const_mul K)]
    exact integral_congr_ae (hst.mono fun x hx => by dsimp only; rw [hx]; ring)
  rw [heq, ← htd, hνint]
  ring

/-- A continuous function whose distributional Laplacian is bounded above and
below by `K` has a measurable weak Laplacian bounded pointwise by `K`. -/
theorem exists_density_of_two_sided {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContinuousOn u U) {K : ℝ} (hK : 0 ≤ K)
    (hle : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x) → |∫ x, u x * Δ φ x ∂μ| ≤ K * ∫ x, φ x ∂μ) :
    ∃ s : E → ℝ, Measurable s ∧ (∀ x, |s x| ≤ K) ∧ IsWeakSolutionLaplace μ U u s := by
  obtain ⟨F, hF, hpair⟩ := exists_l1_extension_of_two_sided (μ := μ) hU hu hK hle
  obtain ⟨s, hsm, hsb, hs⟩ := exists_bounded_density_of_l1 (μ := μ) F hK hF
  refine ⟨s, hsm, hsb, fun φ hφ hφc hφU => ?_⟩
  let ψ : smoothTestSpace U := ⟨φ, hφ, hφc, hφU⟩
  let f : C_c(E, ℝ) := ⟨⟨φ, hφ.continuous⟩, hφc⟩
  exact (hpair ψ).symm.trans (hs f)

end LatticeProb.PegdenSmart
