/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqExist at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqRate
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCBall
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueOpenExist

/-!
# Existence of the LQG measure of the zero-boundary GFF on the unit square (P2-GMC, WP-24)

**Main theorem** (`ae_isVagueLimitOn_qAreaMeasureOn_openSquare`): for `0 < γ < 2` and a QZ
zero-boundary GFF `X` on `𝕍 = (0,1)²`, almost surely the approximating measures
`areaApprox γ (X ω) k = 2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz` converge vaguely on `𝕍`, and
`qAreaMeasureOn γ (X ω) openSquare` (the measure of Statement/Dimension.lean) is their vague limit,
i.e. it is never the junk value `0` of its definition on a full-measure event.

Source: Duplantier–Sheffield arXiv:0808.1560, Prop. 1.1 (a.s. weak convergence of
`ε^{γ²/2} e^{γ h_ε(z)} dz` along `ε = 2^{-k}`, for a zero-boundary GFF on a bounded domain); the
proof follows QZ `AreaExist.ae_exists_isVagueLimitOn_areaApprox` (`AreaExistenceAS.lean`): `L¹`
rate on dyadic scales (`GMCSqRate.lean`) ⇒ a.s. convergence of each test integral
(QZ `AreaExist.ae_tendsto_of_L1_rate`), a countable dense family with cut-offs and the
Riesz–Markov step (QZ `VagueOpen.exists_isVagueLimitOn_of_cutoff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper Real
open scoped ENNReal NNReal

namespace LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → Measure ℂ → ℝ}

lemma exists_radius_le {s : ℝ} (hs : 0 < s) : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → 4 * radius k ≤ s := by
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (show 0 < s / 4 by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨k₀, fun k hk => ?_⟩
  have := (AreaExist.aradius_anti hk).trans hk₀.le
  unfold radius at this ⊢; linarith

/-- **a.s. convergence of each test integral** -/
theorem ae_tendsto_areaApprox_sq (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ openSquare) :
    ∀ᵐ ω ∂P, ∃ l, Tendsto (fun k => ∫ z, f z ∂(areaApprox γ (X ω) k)) atTop (𝓝 l) := by
  obtain ⟨s, hs, hTs⟩ := exists_sqIn_of_isCompact hfc hfU
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM' : ∀ z, |f z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  have hfS : ∀ z ∉ tsupport f, f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  obtain ⟨C, -, hC⟩ := integral_abs_areaApprox_step_le_rate_sq hX hγ hγ2 hs
    (isClosed_tsupport f).measurableSet hfc.isCompact.measure_lt_top hTs hf.measurable hM' hfS
  obtain ⟨k₀, hk₀⟩ := exists_radius_le hs
  set q := exp (-AreaExist.areaRate γ * log 2) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (mul_neg_of_neg_of_pos
    (neg_neg_of_pos (AreaExist.areaRate_pos hγ hγ2)) (log_pos one_lt_two))
  refine AreaExist.ae_tendsto_of_L1_rate (C := C) (exp_pos _).le hq1
    (fun k hk => integrable_integral_areaApprox_sq hX hs (isClosed_tsupport f).measurableSet
      hfc.isCompact.measure_lt_top hTs γ hf.measurable hM' hfS (hk₀ k hk)) fun k hk => ?_
  have := hC k (hk₀ k hk)
  have e : exp (-AreaExist.areaRate γ * (k * log 2)) = q ^ k := by
    rw [hq, ← exp_nat_mul]; congr 1; ring
  rw [e] at this
  refine le_trans (le_of_eq ?_) this
  congr 1; funext ω; rw [abs_sub_comm]

/-- the approximating measures are a.s. finite on each `sqIn (1/(n+2))` at fine scales -/
theorem ae_areaApprox_sqIn_lt_top (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ) (n k : ℕ)
    (hk : radius k < 1 / ((n : ℝ) + 2) / 2) :
    ∀ᵐ ω ∂P, areaApprox γ (X ω) k (sqIn (1 / ((n : ℝ) + 2))) < ∞ := by
  set T := sqIn (1 / ((n : ℝ) + 2))
  have hs : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have hT : MeasurableSet T := (isClosed_sqIn _).measurableSet
  have hm : Measurable fun ω => areaApprox γ (X ω) k T :=
    (Measure.measurable_coe hT).comp ((measurable_areaApprox γ k).comp (measurable_field hX))
  refine ae_lt_top hm (ne_top_of_le_ne_top (ENNReal.mul_ne_top (gmcConst_lt_top γ).ne
    ((isCompact_sqIn hs).measure_lt_top (μ := volume)).ne) ?_)
  have hD := measurable_areaDens hX γ k
  have hrw : ∀ ω, areaApprox γ (X ω) k T = ∫⁻ z, T.indicator 1 z * areaDens γ (X ω) k z
      ∂volume.restrict H := fun ω => by
    have hDω : Measurable (areaDens γ (X ω) k) := (hD.comp measurable_prodMk_left :)
    rw [← lintegral_indicator_one hT, show areaApprox γ (X ω) k =
      (volume.restrict H).withDensity (areaDens γ (X ω) k) from rfl,
      lintegral_withDensity_eq_lintegral_mul _ hDω (measurable_one.indicator hT)]
    congr 1; funext z; simp [mul_comm]
  simp_rw [hrw]
  rw [lintegral_lintegral_swap (((measurable_one.indicator hT).comp measurable_snd).mul
    hD).aemeasurable]
  calc ∫⁻ z, ∫⁻ ω, T.indicator 1 z * areaDens γ (X ω) k z ∂P ∂volume.restrict H
      ≤ ∫⁻ z, T.indicator (fun _ => gmcConst γ) z ∂volume.restrict H := by
        refine lintegral_mono fun z => ?_
        rw [lintegral_const_mul _ (measurable_areaDens_left hX γ k z)]
        by_cases hz : z ∈ T
        · rw [indicator_of_mem hz, indicator_of_mem hz, Pi.one_apply, one_mul]
          exact lintegral_areaDens_le hX γ hs hk hz
        · rw [indicator_of_notMem hz, indicator_of_notMem hz, zero_mul]
    _ = gmcConst γ * volume.restrict H T := by
        rw [lintegral_indicator_const hT]
    _ ≤ gmcConst γ * volume T := mul_le_mul_right (Measure.restrict_le_self T) _

/-- **a.s. existence of the vague limit on the open square** -/
theorem ae_exists_isVagueLimitOn_openSquare (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitOn openSquare (areaApprox γ (X ω)) μ := by
  obtain ⟨F, hFc, hF⟩ := VagueH.exists_denseTestFamily
  have hconv : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ g ∈ F, ∃ l,
      Tendsto (fun k => ∫ z, sqCut n z * g z ∂(areaApprox γ (X ω) k)) atTop (𝓝 l) := by
    rw [ae_all_iff]; intro n
    rw [ae_ball_iff hFc]; intro g hg
    obtain ⟨hgc, hgs, -⟩ := hF.1 g hg
    exact ae_tendsto_areaApprox_sq hX hγ hγ2 ((continuous_sqCut n).mul hgc) hgs.mul_left
      (tsupport_mul_subset_left.trans (tsupport_sqCut_subset_openSquare n))
  have hfin0 : ∀ᵐ ω ∂P, ∀ n k : ℕ, radius k < 1 / ((n : ℝ) + 2) / 2 →
      areaApprox γ (X ω) k (sqIn (1 / ((n : ℝ) + 2))) < ∞ := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    by_cases hk : radius k < 1 / ((n : ℝ) + 2) / 2
    · filter_upwards [ae_areaApprox_sqIn_lt_top hX γ n k hk] with ω h _ using h
    · exact ae_of_all _ fun ω h => absurd h hk
  filter_upwards [hconv, hfin0] with ω h1 h2
  have hr : Tendsto radius atTop (𝓝 0) := by
    unfold radius; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  -- compact subsets of the square
  have hsq : ∀ K, IsCompact K → K ⊆ openSquare → ∃ n : ℕ, K ⊆ sqIn (2 / ((n : ℝ) + 2)) := by
    intro K hK hKU
    obtain ⟨s, hs, hKs⟩ := exists_sqIn_of_isCompact hK hKU
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / s)
    refine ⟨n, hKs.trans fun z ⟨a, b, c, d⟩ => ?_⟩
    have : 2 / ((n : ℝ) + 2) ≤ s := by
      rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ hs] at hn; nlinarith
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine VagueOpen.exists_isVagueLimitOn_of_cutoff isOpen_openSquare openSquare_subset_H
    continuous_sqCut sqCut_nonneg sqCut_le_one tsupport_sqCut_subset_openSquare ?_ hF ?_ h1
  · intro K hK hKU
    obtain ⟨n, hn⟩ := hsq K hK hKU
    exact ⟨n, fun z hz => sqCut_eq_one (hn hz)⟩
  · intro K hK hKU
    obtain ⟨n, hn⟩ := hsq K hK hKU
    have hsub : K ⊆ sqIn (1 / ((n : ℝ) + 2)) := hn.trans fun z ⟨a, b, c, d⟩ => by
      have : 1 / ((n : ℝ) + 2) ≤ 2 / ((n : ℝ) + 2) :=
        div_le_div_of_nonneg_right (by norm_num) (by positivity)
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    filter_upwards [hr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / ((n : ℝ) + 2) / 2 by
      positivity))] with k hk
    exact (measure_mono hsub).trans_lt (h2 n k hk)

/-- **The LQG measure of the frozen d_γ definition is a.s. the vague limit**: for `0 < γ < 2`,
`qAreaMeasureOn γ (X ω) openSquare` is a.s. a vague limit of `areaApprox γ (X ω)` on `𝕍`. -/
theorem ae_isVagueLimitOn_qAreaMeasureOn_openSquare (hX : IsZeroBoundaryGFFOn openSquare X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, IsVagueLimitOn openSquare (areaApprox γ (X ω))
      (qAreaMeasureOn γ (X ω) openSquare) := by
  filter_upwards [ae_exists_isVagueLimitOn_openSquare hX hγ hγ2] with ω h
  unfold qAreaMeasureOn
  rw [dif_pos h]
  exact h.choose_spec

end LQGMetric
