/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DGCmp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGLow
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1C3

/-!
# `WPPhiCompare` from the free-kernel form of DGo Prop 3.3 (task P2-DDDFDG)

The comparison `S6DG.WPPhiCompare` between `φ_{0,K} = φ_{2^{-K},1}` (DDDF's white-noise field,
DG's `ĥ_δ`) and the circle average `h_{2^{-K}}` of a normalized whole-plane GFF splits, exactly as
in the proof of DG Lemma 3.7 (DG:1104–1106: "the uniform comparison between `h_δ` and `ĥ_δ`
[DGo Prop 3.2] together with the continuity estimate for `ĥ_δ`"), into three pieces on the coupling
of DG Lemma 3.1 (`DG.exists_wn_wholePlaneGFF`: `h₀(φ) = W(kerFun φ)`, `h = h₀ − h₀_1(0)`):

1. `h − ĥ` is a continuous field on `[−1,2]²` with a Gaussian tail (DG Lemma 3.1 for the pair
   `(h, ĥ)`, `DG.dgCircMod_h0_hat` and `DG.dgCircMod_const`, proved), so
   `|h_δ(z) − ĥ(σ_{z,δ})| ≤ max_{[−1,2]²} |h − ĥ| = O(1)`;
2. `ĥ(σ_{z,δ}) − ĥ_δ(z)` (circle average of the full white-noise field `ĥ` minus its truncation at
   time `δ²`): this is DGo Prop 3.3 (`prop:coupling`, DGo:549–555) with the free heat kernel on
   `[0,1]` in time in place of `p^𝒰` — the open input `FreeDGoCompare`;
3. the continuity estimate for `ĥ_δ` at scale `Cδ` (`phiMN_osc_tendsto`, from DDDF (2.17)).

The pointwise a.s. identities are upgraded to all `z ∈ [0,1]²` through a countable dense subset and
the continuity of `h_δ`, `ĥ_δ` and of the modification in item 2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6DG

open WhiteNoise GFFExist DZZ QuantumZipper SupTail CircleAvg KilledHeat GMCIdent DG

/-- **Free-kernel DGo Prop 3.3** (DGo `prop:coupling`, DGo:549–555, with `𝒰 = ℂ`): for every white
noise, the difference `Δ_K(z) = ĥ(σ_{z,2^{-K}}) − ĥ_{2^{-K}}(z)` between the circle average of
`ĥ` (DG (3.1), times `(0,1]`) and the truncated field `φ_{0,K}` has a modification continuous on
`[0,1]²` with `max_{[0,1]²} |Δ_K| ≤ ζ K` with probability tending to `1`, for each `ζ > 0`
(DGo: `max_V |Δ_δ| ≤ K√(log δ⁻¹) + x` with Gaussian tail in `x`). -/
def FreeDGoCompare : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
    ∃ D : ℕ → ℂ → Ω → ℝ, (∀ K ω, ContinuousOn (fun z => D K z ω) (rectAB 1 1).toSet) ∧
      (∀ K, ∀ z ∈ (rectAB 1 1).toSet,
        D K z =ᵐ[P] fun ω => dgHat W z ((2 : ℝ)⁻¹ ^ K) ω - phiMN W P 0 K z ω) ∧
      ∀ ζ : ℝ, 0 < ζ → Tendsto (fun K : ℕ =>
        P {ω | ¬ ∀ z ∈ (rectAB 1 1).toSet, |D K z ω| ≤ ζ * K}) atTop (𝓝 0)

lemma closedBall_subset_bigBox {z : ℂ} (hz : z ∈ (rectAB 1 1).toSet) {δ : ℝ} (hδ1 : δ ≤ 1) :
    Metric.closedBall z δ ⊆ ferniqueBox ⟨-1, -1⟩ 3 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add] at hz
  have h1 := (Complex.abs_re_le_norm (x - z)).trans hx
  have h2 := (Complex.abs_im_le_norm (x - z)).trans hx
  rw [Complex.sub_re, abs_le] at h1
  rw [Complex.sub_im, abs_le] at h2
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> norm_num <;> linarith [h1.1, h1.2, h2.1, h2.2, hz.1.1, hz.1.2,
    hz.2.1, hz.2.2]

lemma tendsto_gauss_tail {c₀ c₁ ζ : ℝ} (hc₁ : 0 < c₁) (hζ : 0 < ζ) :
    Tendsto (fun K : ℕ => ENNReal.ofReal (c₀ * Real.exp (-c₁ * (ζ * K) ^ 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun K : ℕ => c₁ * (ζ * K) ^ 2) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hζ)).const_mul_atTop hc₁
  have h2 : Tendsto (fun K : ℕ => c₀ * Real.exp (-c₁ * (ζ * K) ^ 2)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul c₀
    rw [mul_zero] at this
    refine this.congr fun K => ?_
    simp only [Function.comp, neg_mul]
  simpa using ENNReal.tendsto_ofReal h2

/-- **`WPPhiCompare` from the free-kernel DGo Prop 3.3**, on the coupling of DG Lemma 3.1. -/
theorem wpPhiCompare_of_free (hD : FreeDGoCompare) : WPPhiCompare := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := exists_wn_wholePlaneGFF
  set P := LQGDimension.ExistAsm.stdP
  have := hW.isProbabilityMeasure
  have hcm : Measurable fun ω => -circleAvg (h₀ ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  set h : (ℕ → ℝ) → DistC := fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)
  have hN : IsNormalizedWPGFF h P := by
    refine ⟨hh.addConst hcm, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
    simp only [h]
    rw [hω, add_neg_cancel]
  obtain ⟨hc, hcG, -, hver⟩ := exists_isGFFCircleAverage_normalized hN
  obtain ⟨Y1, hY1c, -, ⟨a₀, a₁, ha₁, hT1⟩, hY1⟩ :=
    dgCircMod_h0_hat hW hh hae (y := ⟨-1, -1⟩) (b := 3) (by norm_num)
  obtain ⟨Y2, hY2c, -, ⟨b₀, b₁, hb₁, hT2⟩, hY2⟩ :=
    dgCircMod_const hW hh hae (y := ⟨-1, -1⟩) (b := 3) (by norm_num)
  obtain ⟨c₀, c₁, hc₁, hT⟩ := tail_sub_le ha₁ hb₁ hT1 hT2
  obtain ⟨D, hDc, hDae, hDt⟩ := hD P W hW
  refine ⟨ℕ → ℝ, inferInstance, P, W, h, hc, hW, hN, hcG, hver, fun C hC ζ hζ => ?_⟩
  set S := (rectAB 1 1).toSet with hSdef
  obtain ⟨T, hTS, hTc, hST⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hζ3 : 0 < ζ / 3 := by positivity
  have h1 := phiMN_osc_tendsto hW hC hζ3
  have h2 := hDt (ζ / 3) hζ3
  have h3 := tendsto_gauss_tail (c₀ := c₀) hc₁ hζ3
  have hsum := (h1.add h2).add h3
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) fun K => ?_
  set δ : ℝ := (2 : ℝ)⁻¹ ^ K with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hv := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hNK : ∀ᵐ ω ∂P, ∀ z ∈ T, hc δ z ω - phiMN W P 0 K z ω - D K z ω =
      ∫ x, (Y1 x ω - Y2 x ω) ∂circleUnif z δ := by
    refine (ae_ball_iff hTc).2 fun z hz => ?_
    have hzS := hTS hz
    have hB := closedBall_subset_bigBox hzS hδ1
    filter_upwards [hver δ hδ0 z, ae_circleAvg_addConst hh z hδ0, hY1 z δ hδ0 hB,
      hY2 z δ hδ0 hB, hDae K z hzS] with ω e1 e2 e3 e4 e5
    rw [integral_sub (integrable_circleUnif_of_continuous (hY1c ω) hδ0)
      (integrable_circleUnif_of_continuous (hY2c ω) hδ0), e3, e4, e1, e5]
    simp only [h]
    rw [e2]
    ring
  have hNK0 := ae_iff.1 hNK
  have hsub : {ω | ¬ ∀ z ∈ S, ∀ w ∈ S, ‖z - w‖ ≤ C * δ →
        |hc δ z ω - phiMN W P 0 K w ω| ≤ ζ * K} ⊆
      (({ω | ¬ ∀ z ∈ S, ∀ w ∈ S, ‖z - w‖ ≤ C * δ →
          |phiMN W P 0 K z ω - phiMN W P 0 K w ω| ≤ ζ / 3 * K} ∪
        {ω | ¬ ∀ z ∈ S, |D K z ω| ≤ ζ / 3 * K}) ∪
        {ω | ¬ ∀ z ∈ ferniqueBox ⟨-1, -1⟩ 3, |Y1 z ω - Y2 z ω| ≤ ζ / 3 * K}) ∪
      {ω | ¬ ∀ z ∈ T, hc δ z ω - phiMN W P 0 K z ω - D K z ω =
        ∫ x, (Y1 x ω - Y2 x ω) ∂circleUnif z δ} := by
    intro ω hω
    by_contra hn
    simp only [mem_union, mem_setOf_eq, not_or, not_not] at hn hω
    obtain ⟨⟨⟨hA1, hA2⟩, hA3⟩, hA4⟩ := hn
    apply hω
    -- the comparison on `T`, then on `S` by continuity
    have hT' : ∀ z ∈ T, |hc δ z ω - phiMN W P 0 K z ω - D K z ω| ≤ ζ / 3 * K := by
      intro z hz
      rw [hA4 z hz]
      have hB := closedBall_subset_bigBox (hTS hz) hδ1
      have hae' : ∀ᵐ x ∂circleUnif z δ, ‖Y1 x ω - Y2 x ω‖ ≤ ζ / 3 * K := by
        have h0 : ∀ᵐ x ∂circleUnif z δ, x ∈ Metric.closedBall z δ :=
          mem_ae_iff.2 (circleUnif_compl_closedBall hδ0 z)
        filter_upwards [h0] with x hx
        exact hA3 x (hB hx)
      have := norm_integral_le_of_norm_le_const hae'
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have hFc : ContinuousOn (fun z => |hc δ z ω - phiMN W P 0 K z ω - D K z ω|) S :=
      ((((hcG.continuous δ hδ0 ω).continuousOn).sub (hv.cont ω).continuousOn).sub
        (hDc K ω)).abs
    have hS' : ∀ z ∈ S, |hc δ z ω - phiMN W P 0 K z ω - D K z ω| ≤ ζ / 3 * K := fun z hz =>
      ContinuousWithinAt.closure_le (hST hz) ((hFc z hz).mono hTS) continuousWithinAt_const hT'
    intro z hz w hw hzw
    have e1 := abs_le.1 (hS' z hz)
    have e2 := abs_le.1 (hA2 z hz)
    have e3 := abs_le.1 (hA1 z hz w hw hzw)
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
  have hK0 : (0 : ℝ) ≤ ζ / 3 * K := by positivity
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hNK0, add_zero]
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) (hT (ζ / 3 * K) hK0)

end S6DG
end DDDF
end LQGMetric
