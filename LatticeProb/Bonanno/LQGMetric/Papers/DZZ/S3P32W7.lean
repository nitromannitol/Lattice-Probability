/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W6
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent5Mom

/-!
# D97, packet P-1: from vague convergence on `(0,1)²` to the masses of balls (`IsChaosLimit`)

`IsChaosLimit` (S3L8) asks for convergence of the approximations on every rational ball `B`,
integrated over `B ∩ 𝕍`, also when `B` meets `∂𝕍`. The vague convergence on the open square
(`ae_isVagueLimitOn_wickMeasC`) gives this for balls of null boundary once no mass of the
approximations escapes to `∂𝕍`:

* **`tendsto_ball_of_vague`** (deterministic portmanteau): if `μs → μ` vaguely on `(0,1)²`, the
  `μs n` are finite on compact subsets of `(0,1)²`, `μ(∂B) = 0`, and the strips `𝕍 ∖ sqIn s` have
  eventually small `μs n`-mass (`StripTight`), then `μs n (B ∩ 𝕍) → μ(B)`. Lower bound by the
  cut-offs `cutRamp`, upper bound by Urysohn functions and continuity of `μ` along
  `cthickening`.

Own elementary proof (standard portmanteau argument, Billingsley, *Convergence of Probability
Measures*, Thm 2.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open QuantumZipper

/-- No mass of the approximations escapes to `∂𝕍`. -/
def StripTight (μs : ℕ → Measure ℂ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ s : ℝ, 0 < s ∧ ∀ᶠ n in atTop, μs n (dzzV \ sqIn s) ≤ ε

lemma ofReal_integral_eq_lintegral {ν : Measure ℂ} {g : ℂ → ℝ} (hg : Continuous g)
    (h0 : ∀ z, 0 ≤ g z) (h1 : ∀ z, g z ≤ 1) {C : Set ℂ} (hC : MeasurableSet C)
    (hgC : ∀ z ∉ C, g z = 0) (hν : ν C < ⊤) :
    ENNReal.ofReal (∫ z, g z ∂ν) = ∫⁻ z, ENNReal.ofReal (g z) ∂ν := by
  have hle : ∫⁻ z, ENNReal.ofReal (g z) ∂ν ≤ ν C := by
    rw [← lintegral_indicator_one hC]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ C
    · rw [indicator_of_mem hz, Pi.one_apply]; exact ENNReal.ofReal_le_one.2 (h1 z)
    · rw [indicator_of_notMem hz, hgC z hz, ENNReal.ofReal_zero]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hg.aestronglyMeasurable,
    ENNReal.ofReal_toReal (hle.trans_lt hν).ne]

/-- Convergence of `∫⁻ g` for a test function `0 ≤ g ≤ 1` of compact support in `(0,1)²`. -/
lemma tendsto_lintegral_of_vague {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hv : IsVagueLimitOn openSquare μs μ)
    (hfin : ∀ n K, IsCompact K → K ⊆ openSquare → μs n K < ⊤) {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ openSquare) (h0 : ∀ z, 0 ≤ g z)
    (h1 : ∀ z, g z ≤ 1) :
    Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (g z) ∂(μs n)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (g z) ∂μ)) := by
  have hC : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
  have hgC : ∀ z ∉ tsupport g, g z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have e : ∀ ν : Measure ℂ, ν (tsupport g) < ⊤ →
      ENNReal.ofReal (∫ z, g z ∂ν) = ∫⁻ z, ENNReal.ofReal (g z) ∂ν := fun ν hν =>
    ofReal_integral_eq_lintegral hg h0 h1 hC hgC hν
  rw [← e μ (hv.2.1 _ hgc hgU)]
  simp_rw [← e _ (hfin _ _ hgc hgU)]
  exact (ENNReal.continuous_ofReal.tendsto _).comp (hv.2.2 g hg hgc hgU)

/-- Lower bound on open sets. -/
lemma eventually_lt_of_open {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hv : IsVagueLimitOn openSquare μs μ)
    (hfin : ∀ n K, IsCompact K → K ⊆ openSquare → μs n K < ⊤) {O : Set ℂ} (hO : IsOpen O)
    (hOU : O ⊆ openSquare) {b : ℝ≥0∞} (hb : b < μ O) : ∀ᶠ n in atTop, b < μs n O := by
  have hmono : Monotone fun k z => ENNReal.ofReal (GMCIdent5.cutRamp O k z) :=
    fun k k' h z => ENNReal.ofReal_le_ofReal (GMCIdent5.cutRamp_mono O z h)
  have hsup : μ O = ⨆ k, ∫⁻ z, ENNReal.ofReal (GMCIdent5.cutRamp O k z) ∂μ := by
    rw [← lintegral_iSup (f := fun k z => ENNReal.ofReal (GMCIdent5.cutRamp O k z))
      (fun k => ENNReal.measurable_ofReal.comp (GMCIdent5.continuous_cutRamp O k).measurable)
      hmono]
    simp_rw [GMCIdent5.iSup_cutRamp hO hOU]
    exact (lintegral_indicator_one hO.measurableSet).symm
  rw [hsup] at hb
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hb
  have ht := tendsto_lintegral_of_vague hv hfin (GMCIdent5.continuous_cutRamp O k)
    (GMCIdent5.hasCompactSupport_cutRamp O k) (GMCIdent5.tsupport_cutRamp O k)
    (GMCIdent5.cutRamp_nonneg O k) (GMCIdent5.cutRamp_le_one O k)
  filter_upwards [(tendsto_order.1 ht).1 b hk] with n hn
  exact hn.trans_le (GMCIdent5.lintegral_cutRamp_le O k (μs n) hO.measurableSet)

/-- Upper bound on compact sets. -/
lemma eventually_lt_of_compact {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hv : IsVagueLimitOn openSquare μs μ)
    (hfin : ∀ n K, IsCompact K → K ⊆ openSquare → μs n K < ⊤) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ openSquare) {b : ℝ≥0∞} (hb : μ K < b) : ∀ᶠ n in atTop, μs n K < b := by
  obtain ⟨r₀, hr₀, hr₀U⟩ := hK.exists_cthickening_subset_open isOpen_openSquare hKU
  have hlim : Tendsto (fun r => μ (cthickening r K)) (𝓝[>] 0) (𝓝 (μ K)) := by
    have := tendsto_measure_cthickening (μ := μ) (s := K)
      ⟨r₀, hr₀, (hv.2.1 _ (hK.cthickening) hr₀U).ne⟩
    rw [hK.isClosed.closure_eq] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨r, ⟨hr0, hrr₀⟩, hrb⟩ : ∃ r ∈ Ioo 0 r₀, μ (cthickening r K) < b := by
    have h1 := (tendsto_order.1 hlim).2 b hb
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 r₀ := Ioo_mem_nhdsGT hr₀
    exact (h1.and h2).exists.imp fun r h => ⟨h.2, h.1⟩
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hK
    (isOpen_thickening (δ := r) (E := K)).isClosed_compl
    (disjoint_compl_right_iff_subset.2 (self_subset_thickening hr0 K))
  have hts : tsupport f ⊆ cthickening r K := by
    refine closure_minimal (fun z hz => ?_) isClosed_cthickening
    by_contra h
    exact hz (hf0 fun h' => h (thickening_subset_cthickening r K h'))
  have hsub : cthickening r K ⊆ openSquare :=
    (cthickening_mono hrr₀.le K).trans hr₀U
  have ht := tendsto_lintegral_of_vague hv hfin f.continuous hfc (hts.trans hsub)
    (fun z => (hf01 z).1) (fun z => (hf01 z).2)
  have hle : ∫⁻ z, ENNReal.ofReal (f z) ∂μ < b := by
    refine lt_of_le_of_lt ?_ hrb
    rw [← lintegral_indicator_one isClosed_cthickening.measurableSet]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ cthickening r K
    · rw [indicator_of_mem hz, Pi.one_apply]; exact ENNReal.ofReal_le_one.2 (hf01 z).2
    · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport (fun h => hz (hts h)),
        ENNReal.ofReal_zero]
  filter_upwards [(tendsto_order.1 ht).2 b hle] with n hn
  refine lt_of_le_of_lt ?_ hn
  rw [← lintegral_indicator_one hK.measurableSet]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ K
  · rw [indicator_of_mem hz, Pi.one_apply, hf1 hz, Pi.one_apply, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]; exact zero_le

lemma openSquare_subset_dzzV : openSquare ⊆ dzzV := fun _ ⟨a, b, c, d⟩ =>
  ⟨a.le, b.le, c.le, d.le⟩

/-- **Portmanteau for balls** (deterministic): vague convergence on `(0,1)²`, finiteness on
compacts, no escape of mass to `∂𝕍` and `μ(∂B) = 0` give `μs n (B ∩ 𝕍) → μ(B)`. -/
theorem tendsto_ball_of_vague {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hv : IsVagueLimitOn openSquare μs μ)
    (hfin : ∀ n K, IsCompact K → K ⊆ openSquare → μs n K < ⊤) (ht : StripTight μs) (x : ℂ)
    (r : ℝ) (hsph : μ (sphere x r) = 0) :
    Tendsto (fun n => μs n (ball x r ∩ dzzV)) atTop (𝓝 (μ (ball x r))) := by
  have hmO : MeasurableSet openSquare := isOpen_openSquare.measurableSet
  have eO : μ (ball x r ∩ openSquare) = μ (ball x r) := by
    refine le_antisymm (measure_mono inter_subset_left) ?_
    rw [← measure_inter_add_sdiff (ball x r) hmO]
    have : μ (ball x r \ openSquare) = 0 :=
      measure_mono_null (fun z hz => hz.2) hv.1
    rw [this, add_zero]
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rw [← eO] at hb
    filter_upwards [eventually_lt_of_open hv hfin (isOpen_ball.inter isOpen_openSquare)
      inter_subset_right hb] with n hn
    exact hn.trans_le (measure_mono (inter_subset_inter_right _ openSquare_subset_dzzV))
  · obtain ⟨c, hc1, hc2⟩ := exists_between hb
    set ε : ℝ≥0∞ := min (b - c) 1 with hε
    have hε0 : 0 < ε := lt_min (tsub_pos_of_lt hc2) one_pos
    have hε1 : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
    have hcε : c + ε ≤ b := by
      calc c + ε ≤ c + (b - c) := by gcongr; exact min_le_left _ _
        _ = b := add_tsub_cancel_of_le hc2.le
    obtain ⟨s, hs, hst⟩ := ht ε hε0
    set K := closedBall x r ∩ sqIn s with hK
    have hKc : IsCompact K := (isCompact_sqIn hs).inter_left isClosed_closedBall
    have hKU : K ⊆ openSquare := inter_subset_right.trans (sqIn_subset_openSquare hs)
    have hμK : μ K < c := by
      refine lt_of_le_of_lt ?_ hc1
      calc μ K ≤ μ (closedBall x r) := measure_mono inter_subset_left
        _ = μ (ball x r ∪ sphere x r) := by rw [ball_union_sphere]
        _ ≤ μ (ball x r) + μ (sphere x r) := measure_union_le _ _
        _ = μ (ball x r) := by rw [hsph, add_zero]
    filter_upwards [eventually_lt_of_compact hv hfin hKc hKU hμK, hst] with n h1 h2
    have hsub : ball x r ∩ dzzV ⊆ K ∪ (dzzV \ sqIn s) := by
      intro z ⟨hz1, hz2⟩
      by_cases hzs : z ∈ sqIn s
      · exact Or.inl ⟨ball_subset_closedBall hz1, hzs⟩
      · exact Or.inr ⟨hz2, hzs⟩
    calc μs n (ball x r ∩ dzzV) ≤ μs n (K ∪ (dzzV \ sqIn s)) := measure_mono hsub
      _ ≤ μs n K + μs n (dzzV \ sqIn s) := measure_union_le _ _
      _ < c + ε := ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top hε1 h2) h1 h2
      _ ≤ b := hcε

end DZZ
end LQGMetric
