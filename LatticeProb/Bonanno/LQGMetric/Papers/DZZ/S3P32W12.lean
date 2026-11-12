/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W11

/-!
# D97, packet P-1: no mass of the approximations escapes to `∂𝕍`; `IsChaosLimit` for `M^W`

* `volume_strip_tendsto`: the strips `𝕍 ∖ sqIn (1/(j+2))` have area `→ 0`;
* **`ae_stripTight`**: a.s. `StripTight (wickMeasC hW γ · ω)`: by Doob's maximal inequality
  (`measure_exists_wickMeas_gt`) `P(sup_n X_n(strip_j) > 2^{-k}) ≤ 2^k Leb(strip_j)`; choosing
  `Leb(strip_{j_k}) ≤ 4^{-k}`, Borel–Cantelli gives a.s. `sup_n X_n(strip_{j_k}) ≤ 2^{-k}` for all
  large `k`;
* **`ae_isChaosLimit_wickQArea`**: a.s. `IsChaosLimit γ ζ tildeVar 2^{-n} (M^W)` for the continuous
  version `ζ = wickZeta hW` of `h̃` (DZZ (eq-def-M-eta), l. 1209–1213).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4 GMCIdent5

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

lemma volume_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h := (Complex.volume_preserving_equiv_real_prod).measure_preimage
    (s := ({c} : Set ℝ) ×ˢ (univ : Set ℝ)) (measurableSet_singleton c |>.prod MeasurableSet.univ).nullMeasurableSet
  have e : Complex.measurableEquivRealProd ⁻¹' (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) =
      {z : ℂ | z.re = c} := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [e] at h
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

lemma volume_im_eq (c : ℝ) : volume {z : ℂ | z.im = c} = 0 := by
  have h := (Complex.volume_preserving_equiv_real_prod).measure_preimage
    (s := (univ : Set ℝ) ×ˢ ({c} : Set ℝ)) (MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet
  have e : Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ ({c} : Set ℝ)) =
      {z : ℂ | z.im = c} := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [e] at h
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- the strips `𝕍 ∖ sqIn (1/(j+2))` -/
def stripJ (j : ℕ) : Set ℂ := dzzV \ sqIn (1 / ((j : ℝ) + 2))

lemma measurableSet_stripJ (j : ℕ) : MeasurableSet (stripJ j) :=
  measurableSet_dzzV.diff (isClosed_sqIn _).measurableSet

lemma volume_stripJ_ne_top (j : ℕ) : volume (stripJ j) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : ℂ)) (r := 2)).ne
    (measure_mono fun z hz => ?_)
  obtain ⟨⟨a, b, c, d⟩, -⟩ := hz
  rw [mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  rw [abs_of_nonneg a, abs_of_nonneg c]; linarith

lemma volume_stripJ_tendsto : Tendsto (fun j => volume (stripJ j)) atTop (𝓝 0) := by
  have hanti : Antitone stripJ := by
    intro j j' h z ⟨hz, hzs⟩
    refine ⟨hz, fun hz' => hzs ?_⟩
    have : 1 / ((j' : ℝ) + 2) ≤ 1 / ((j : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 2)
    obtain ⟨a, b, c, d⟩ := hz'
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have h := tendsto_measure_iInter_atTop (μ := (volume : Measure ℂ))
    (fun j => (measurableSet_stripJ j).nullMeasurableSet) hanti ⟨0, volume_stripJ_ne_top 0⟩
  have h0 : volume (⋂ j, stripJ j) = 0 := by
    refine measure_mono_null (t := ({z : ℂ | z.re = 0} ∪ {z | z.re = 1}) ∪
      ({z : ℂ | z.im = 0} ∪ {z | z.im = 1})) ?_ (measure_union_null
        (measure_union_null (volume_re_eq 0) (volume_re_eq 1))
        (measure_union_null (volume_im_eq 0) (volume_im_eq 1)))
    intro z hz
    have hV := (mem_iInter.1 hz 0).1
    obtain ⟨a, b, c, d⟩ := hV
    by_contra hne
    simp only [mem_union, mem_ofPred_eq, not_or] at hne
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hne
    have p1 : 0 < z.re := lt_of_le_of_ne a (Ne.symm h1)
    have p2 : z.re < 1 := lt_of_le_of_ne b h2
    have p3 : 0 < z.im := lt_of_le_of_ne c (Ne.symm h3)
    have p4 : z.im < 1 := lt_of_le_of_ne d h4
    set t := min (min z.re (1 - z.re)) (min z.im (1 - z.im))
    have ht : 0 < t := lt_min (lt_min p1 (by linarith)) (lt_min p3 (by linarith))
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / t)
    have hjt : 1 / ((j : ℝ) + 2) ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ ht] at hj; nlinarith
    refine (mem_iInter.1 hz j).2 ⟨?_, ?_, ?_, ?_⟩
    · exact hjt.trans ((min_le_left _ _).trans (min_le_left _ _))
    · have := hjt.trans ((min_le_left _ _).trans (min_le_right _ _)); linarith
    · exact hjt.trans ((min_le_right _ _).trans (min_le_left _ _))
    · have := hjt.trans ((min_le_right _ _).trans (min_le_right _ _)); linarith
  rw [h0] at h
  exact h

/-- **a.s. no mass of the approximations escapes to `∂𝕍`.** -/
theorem ae_stripTight (hW : IsWhiteNoise P' W) (γ : ℝ) :
    ∀ᵐ ω ∂P', StripTight fun n => wickMeasC hW γ n ω := by
  have hP := hW.isProbabilityMeasure
  set ε : ℕ → ℝ≥0 := fun k => (2⁻¹ : ℝ≥0) ^ k
  have hεpos : ∀ k, 0 < ((ε k : ℝ≥0) : ℝ≥0∞) := fun k =>
    ENNReal.coe_pos.2 (pow_pos (by norm_num) k)
  have hq : ∀ k : ℕ, ∃ j, volume (stripJ j) ≤ (ε k : ℝ≥0∞) * (ε k) := fun k =>
    ((tendsto_order.1 volume_stripJ_tendsto).2 _ (ENNReal.mul_pos (hεpos k).ne'
      (hεpos k).ne')).exists.imp fun _ h => h.le
  choose J hJ using hq
  set A : ℕ → Set Ω' := fun k => {ω | ∃ n, (ε k : ℝ) < wickProc W γ (stripJ (J k)) n ω}
  have hA : ∀ k, P' (A k) ≤ (ε k : ℝ≥0∞) := by
    intro k
    have hε0 : (ε k : ℝ≥0∞) ≠ 0 := (hεpos k).ne'
    have hD := measure_exists_wickMeas_gt hW γ (measurableSet_stripJ (J k))
      (volume_stripJ_ne_top (J k)) (ε k)
    have h1 : P' (A k) ≤ volume (stripJ (J k)) / (ε k) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl ENNReal.coe_ne_top)).2
        (by rw [mul_comm]; exact hD)
    exact h1.trans (ENNReal.div_le_of_le_mul (hJ k))
  have hsum : ∑' k, P' (A k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
    exact ENNReal.tsum_coe_ne_top_iff_summable.2
      (NNReal.summable_geometric (by norm_num : (2⁻¹ : ℝ≥0) < 1))
  have hfin : ∀ᵐ ω ∂P', ∀ n k, wickMeas W γ n ω (stripJ (J k)) < ⊤ := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k
    exact ae_lt_top (measurable_wickMeas_apply hW γ n (measurableSet_stripJ (J k)))
      (by rw [lintegral_wickMeas hW γ n (measurableSet_stripJ (J k))]
          exact volume_stripJ_ne_top _)
  filter_upwards [ae_eventually_notMem hsum, hfin, ae_wickMeas_eq_wickMeasC hW γ]
    with ω hev hf he e he0
  have hε : Tendsto (fun k => ((ε k : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_coe.2
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2⁻¹ : ℝ≥0) < 1))
    rw [ENNReal.coe_zero] at this
    exact this
  obtain ⟨k, hk1, hk2⟩ := (hev.and ((tendsto_order.1 hε).2 e he0)).exists
  refine ⟨1 / ((J k : ℝ) + 2), by positivity, Eventually.of_forall fun n => ?_⟩
  show wickMeasC hW γ n ω (stripJ (J k)) ≤ e
  rw [← he n]
  have hle : wickProc W γ (stripJ (J k)) n ω ≤ (ε k : ℝ) := by
    by_contra h; push Not at h; exact hk1 ⟨n, h⟩
  have hX : wickMeas W γ n ω (stripJ (J k)) ≤ (ε k : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal (hf n k).ne, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hle
  exact hX.trans hk2.le

/-- **P-1: `IsChaosLimit` for `M^W`** (DZZ (eq-def-M-eta), l. 1209–1213): a.s. `M^W` is the limit of
`∫_{B ∩ 𝕍} e^{γ h̃_{2^{-n}} − γ²/2 Var h̃_{2^{-n}}} dz` on every rational ball `B`, for the continuous
version `wickZeta hW` of `h̃` (`wickZeta_spec`). -/
theorem ae_isChaosLimit_wickQArea (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P', IsChaosLimit γ (fun s z => wickZeta hW s z ω) tildeVar
      (fun n => (1 / 2 : ℝ) ^ n) (wickQArea γ W ω) :=
  isChaosLimit_wickQArea_of_tight hW hγ hγ2 (ae_stripTight hW γ)

end DZZ
end LQGMetric
