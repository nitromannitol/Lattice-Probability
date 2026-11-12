/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117G3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Geom

/-!
# DZZ Lemma 5.3, part 3: the coupling `DZZTildeCouple` (packet P-53T, DEC-117 §2(d))

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2423 ("By Proposition 3.2,
Lemmas 2.9, 3.8, 3.10 and Corollary 3.9, `χ` does not depend on `u, v`") and lem-scaling-coupling
(l. 611–624). Decision DEC-117 §2(d): `DZZTildeCouple` is the scaling coupling `DZZSimCoupleU`
(proved for `0 < ‖a‖ ≤ 1` as `dzzSimCoupleU_of_norm_le`, S5D117G3) for the similarity
`θ = simMap a b` with `θ(𝕍̃_{u,v}) = 𝕍̃_{u',v'}`, `θ u = u'`, `θ v = v'`, in sandwich form.

This file (geometry and generic probability):
* `simMap_image_tildeBox`: a similarity maps `𝕍̃_{u,v}` onto `𝕍̃_{θu,θv}`;
* `tildeBox_subset_dzzVXi`: `𝕍̃_{u,v} ⊆ 𝕍^{1/4}` for `u ≠ v ∈ 𝕍̄`;
* `tendsto_prob_shift`: if `E Y_δ / log δ⁻¹ → χ` and `Y_δ` is a.s. antitone in `δ`, then
  `|Y_{cδ} − Y_δ| = o(log δ⁻¹)` in probability for every fixed `c > 0` (Markov: the difference
  has a sign, so its mean is the difference of the means, which is `o(log δ⁻¹)`);
* `tendsto_close_of_sandwich`: the sandwich `Y_{sδe^λ} ≤ X_δ ≤ Y_{sδe^{−λ}}` outside an event of
  probability `≤ η` (any `η > 0`, `λ = λ(η)` fixed) gives `|X_δ − Y_δ| = o(log δ⁻¹)` in
  probability.

The way the δ-shift is absorbed (a.s. monotonicity in `δ` plus the existence of the per-pair
limit, then Markov) is our own elementary argument following DEC-117 §2(d); DZZ do not spell it
out (they cite Cor 3.9).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ComplexConjugate

namespace LQGMetric
namespace DZZ

/-! ### Geometry of the tilde boxes -/

lemma simMap_mem_tildeBox_iff {a : ℂ} (ha : a ≠ 0) (b z u v : ℂ) :
    simMap a b z ∈ tildeBox (simMap a b u) (simMap a b v) ↔ z ∈ tildeBox u v := by
  have hn : 0 < ‖a‖ ^ 2 := by positivity
  have e1 : (simMap a b z - (simMap a b u + simMap a b v) / 2) *
      starRingEnd ℂ (simMap a b v - simMap a b u) =
      ((‖a‖ ^ 2 : ℝ) : ℂ) * ((z - (u + v) / 2) * starRingEnd ℂ (v - u)) := by
    push_cast
    rw [← Complex.mul_conj']
    simp only [simMap, map_sub, map_mul, map_add]
    ring
  have e2 : ‖simMap a b v - simMap a b u‖ ^ 2 = ‖a‖ ^ 2 * ‖v - u‖ ^ 2 := by
    simp only [simMap, add_sub_add_right_eq_sub, ← mul_sub, norm_mul, mul_pow]
  simp only [tildeBox, mem_ofPred_eq, e1, e2, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    abs_mul, abs_of_pos hn, mul_le_mul_iff_of_pos_left hn]

/-- A similarity maps `𝕍̃_{u,v}` onto `𝕍̃_{θu,θv}`. -/
lemma simMap_image_tildeBox {a : ℂ} (ha : a ≠ 0) (b u v : ℂ) :
    simMap a b '' tildeBox u v = tildeBox (simMap a b u) (simMap a b v) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (simMap_mem_tildeBox_iff ha b z u v).2 hz
  · intro hw
    have hz : simMap a b ((w - b) / a) = w := by
      simp only [simMap]; field_simp; ring
    refine ⟨(w - b) / a, (simMap_mem_tildeBox_iff ha b _ u v).1 (by rwa [hz]), hz⟩

lemma mem_tildeBox_left (u v : ℂ) : u ∈ tildeBox u v := by
  have e : (u - (u + v) / 2) * starRingEnd ℂ (v - u) = ((-(‖v - u‖ ^ 2 / 2) : ℝ) : ℂ) := by
    have := Complex.mul_conj' (v - u)
    push_cast
    linear_combination (-1 / 2 : ℂ) * this
  simp only [tildeBox, mem_ofPred_eq, e, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
  refine ⟨?_, by positivity⟩
  rw [abs_neg, abs_of_nonneg (by positivity)]
  linarith [sq_nonneg ‖v - u‖]

lemma mem_tildeBox_right (u v : ℂ) : v ∈ tildeBox u v := by
  have e : (v - (u + v) / 2) * starRingEnd ℂ (v - u) = (((‖v - u‖ ^ 2 / 2) : ℝ) : ℂ) := by
    have := Complex.mul_conj' (v - u)
    push_cast
    linear_combination (1 / 2 : ℂ) * this
  simp only [tildeBox, mem_ofPred_eq, e, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
  refine ⟨?_, by positivity⟩
  rw [abs_of_nonneg (by positivity)]
  linarith [sq_nonneg ‖v - u‖]

/-- `𝕍̃_{u,v} ⊆ 𝕍^{1/4}` for `u ≠ v ∈ 𝕍̄`: points of `𝕍̃_{u,v}` are within `2|u − v| ≤ 1/5` of
the midpoint, which is within `1/40` of the centre of `𝕍`. -/
lemma tildeBox_subset_dzzVXi {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) :
    tildeBox u v ⊆ dzzVXi (1 / 4) := by
  intro z hz
  obtain ⟨hu1, hu2⟩ := near_of_mem_dzzVbar hu
  obtain ⟨hv1, hv2⟩ := near_of_mem_dzzVbar hv
  have hd : 0 < ‖v - u‖ := norm_pos_iff.2 (sub_ne_zero.2 huv.symm)
  have hw := (Complex.norm_le_abs_re_add_abs_im ((z - (u + v) / 2) * starRingEnd ℂ (v - u))).trans
    (add_le_add hz.1 hz.2)
  rw [norm_mul, Complex.norm_conj] at hw
  have hzm : ‖z - (u + v) / 2‖ ≤ 2 * ‖v - u‖ := by
    by_contra h
    push Not at h
    nlinarith
  have hd' : ‖v - u‖ ≤ 1 / 10 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    rw [abs_le] at hu1 hu2 hv1 hv2
    have h1 : |v.re - u.re| ≤ 1 / 20 := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : |v.im - u.im| ≤ 1 / 20 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hre := Complex.abs_re_le_norm (z - (u + v) / 2)
  have him := Complex.abs_im_le_norm (z - (u + v) / 2)
  simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.add_re, Complex.add_im] at hre him
  rw [abs_le] at hu1 hu2 hv1 hv2 hre him
  refine mem_dzzVXi_of_near (a := 9 / 40) ?_ ?_ (by norm_num) (by norm_num) <;>
    rw [abs_le] <;> constructor <;> linarith

/-! ### Generic probability: absorbing a fixed δ-shift -/

lemma tendsto_log_inv_nhdsGT : Tendsto (fun δ : ℝ => Real.log δ⁻¹) (𝓝[>] 0) atTop := by
  refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun δ => ?_
  simp [Real.log_inv]

lemma tendsto_const_mul_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ : ℝ => c * δ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun δ hδ => mul_pos hc hδ⟩
  have : Tendsto (fun δ : ℝ => c * δ) (𝓝[>] 0) (𝓝 (c * 0)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).const_mul c
  simpa using this

/-- If `f(δ)/log δ⁻¹ → χ` then `f(cδ)/log δ⁻¹ → χ` for fixed `c > 0`. -/
lemma tendsto_shift_div_log {f : ℝ → ℝ} {χ c : ℝ} (hc : 0 < c)
    (hf : Tendsto (fun δ => f δ / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)) :
    Tendsto (fun δ => f (c * δ) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ) := by
  have hL := tendsto_log_inv_nhdsGT
  have h1 := hf.comp (tendsto_const_mul_nhdsGT hc)
  have h2 : Tendsto (fun δ : ℝ => 1 + Real.log c⁻¹ / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hL)
  rw [add_zero] at h2
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hL.eventually (eventually_gt_atTop 0),
    (hL.comp (tendsto_const_mul_nhdsGT hc)).eventually (eventually_gt_atTop 0)] with δ hδ h0 h0'
  simp only [Function.comp_apply] at h0' ⊢
  have e : Real.log (c * δ)⁻¹ = Real.log c⁻¹ + Real.log δ⁻¹ := by
    rw [mul_inv, Real.log_mul (inv_ne_zero hc.ne') (inv_ne_zero (ne_of_gt hδ))]
  rw [e] at h0' ⊢
  rw [show 1 + Real.log c⁻¹ / Real.log δ⁻¹ = (Real.log c⁻¹ + Real.log δ⁻¹) / Real.log δ⁻¹ by
    rw [add_div, div_self h0.ne', add_comm], div_mul_div_comm,
    mul_comm (Real.log c⁻¹ + Real.log δ⁻¹), mul_div_mul_right _ _ h0'.ne']

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **A fixed δ-shift costs `o(log δ⁻¹)` in probability** (own elementary argument, DEC-117
§2(d)): if `Y_δ` is a.s. antitone in `δ` and `E Y_δ / log δ⁻¹ → χ`, then for fixed `c > 0`,
`P(|Y_{cδ} − Y_δ| > ε log δ⁻¹) → 0`. -/
theorem tendsto_prob_shift [IsProbabilityMeasure P] {Y : ℝ → Ω → ℝ} {χ c : ℝ} (hc : 0 < c)
    (hYi : ∀ δ, 0 < δ → Integrable (Y δ) P)
    (hanti : ∀ δ δ', 0 < δ → δ ≤ δ' → ∀ᵐ ω ∂P, Y δ' ω ≤ Y δ ω)
    (hlim : Tendsto (fun δ => (∫ ω, Y δ ω ∂P) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ => P {ω | ε * Real.log δ⁻¹ < |Y (c * δ) ω - Y δ ω|}) (𝓝[>] 0) (𝓝 0) := by
  have hL := tendsto_log_inv_nhdsGT
  have hR : Tendsto (fun δ => 1 / ε * |(∫ ω, Y (c * δ) ω ∂P) / Real.log δ⁻¹ -
      (∫ ω, Y δ ω ∂P) / Real.log δ⁻¹|) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_shift_div_log hc hlim).sub hlim).abs.const_mul (1 / ε)
    simpa using this
  have hreal : Tendsto (fun δ => P.real {ω | ε * Real.log δ⁻¹ < |Y (c * δ) ω - Y δ ω|})
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
      (Eventually.of_forall fun δ => measureReal_nonneg) ?_
    filter_upwards [self_mem_nhdsWithin, hL.eventually (eventually_gt_atTop 0)] with δ hδ hL0
    have hcδ : 0 < c * δ := mul_pos hc hδ
    have hint : Integrable (fun ω => |Y (c * δ) ω - Y δ ω|) P :=
      ((hYi _ hcδ).sub (hYi δ hδ)).abs
    have hM := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _)
      hint (ε * Real.log δ⁻¹)
    have hI : ∫ ω, |Y (c * δ) ω - Y δ ω| ∂P ≤
        |(∫ ω, Y (c * δ) ω ∂P) - ∫ ω, Y δ ω ∂P| := by
      rcases le_total c 1 with h1 | h1
      · have hle := hanti (c * δ) δ hcδ (by nlinarith)
        rw [integral_congr_ae (hle.mono fun ω h => abs_of_nonneg (sub_nonneg.2 h)),
          integral_sub (hYi _ hcδ) (hYi δ hδ)]
        exact le_abs_self _
      · have hle := hanti δ (c * δ) hδ (by nlinarith)
        rw [integral_congr_ae (hle.mono fun ω h => abs_of_nonpos (sub_nonpos.2 h)),
          integral_neg, integral_sub (hYi _ hcδ) (hYi δ hδ)]
        exact neg_le_abs _
    have hmono : P.real {ω | ε * Real.log δ⁻¹ < |Y (c * δ) ω - Y δ ω|} ≤
        P.real {ω | ε * Real.log δ⁻¹ ≤ |Y (c * δ) ω - Y δ ω|} :=
      measureReal_mono fun ω (h : ε * Real.log δ⁻¹ < _) =>
        show ε * Real.log δ⁻¹ ≤ _ from h.le
    have hεL : 0 < ε * Real.log δ⁻¹ := mul_pos hε hL0
    rw [← sub_div, abs_div, abs_of_pos hL0]
    calc _ ≤ P.real {ω | ε * Real.log δ⁻¹ ≤ |Y (c * δ) ω - Y δ ω|} := hmono
      _ ≤ |(∫ ω, Y (c * δ) ω ∂P) - ∫ ω, Y δ ω ∂P| / (ε * Real.log δ⁻¹) := by
          rw [le_div_iff₀ hεL, mul_comm]; exact hM.trans hI
      _ = _ := by field_simp
  have := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at this
  refine this.congr fun δ => ?_
  exact ofReal_measureReal

/-- **Closeness from a sandwich** (DEC-117 §2(d)): if, for every `η > 0`, there is `λ` with
`Y_{sδe^λ} ≤ X_δ ≤ Y_{sδe^{−λ}}` outside an event of probability `≤ η` (for all `δ > 0`), and `Y`
satisfies the hypotheses of `tendsto_prob_shift`, then `|X_δ − Y_δ| = o(log δ⁻¹)` in
probability. -/
theorem tendsto_close_of_sandwich [IsProbabilityMeasure P] {X Y : ℝ → Ω → ℝ} {s χ : ℝ}
    (hs : 0 < s) (hYi : ∀ δ, 0 < δ → Integrable (Y δ) P)
    (hanti : ∀ δ δ', 0 < δ → δ ≤ δ' → ∀ᵐ ω ∂P, Y δ' ω ≤ Y δ ω)
    (hlim : Tendsto (fun δ => (∫ ω, Y δ ω ∂P) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ))
    (hsand : ∀ η : ℝ, 0 < η → ∃ lam : ℝ, ∀ δ : ℝ, 0 < δ →
      P {ω | ¬ (Y (s * δ * Real.exp lam) ω ≤ X δ ω ∧ X δ ω ≤ Y (s * δ * Real.exp (-lam)) ω)} ≤
        ENNReal.ofReal η)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ => P {ω | ε * Real.log δ⁻¹ < |X δ ω - Y δ ω|}) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  by_cases het : e = ⊤
  · exact Eventually.of_forall fun _ => het ▸ le_top
  set η : ℝ := e.toReal / 3 with hηdef
  have hη : 0 < η := div_pos (ENNReal.toReal_pos he.ne' het) (by norm_num)
  obtain ⟨lam, hlam⟩ := hsand η hη
  have hε2 : 0 < ε / 2 := by linarith
  have h1 := ENNReal.tendsto_nhds_zero.1 (tendsto_prob_shift (mul_pos hs (Real.exp_pos lam))
    hYi hanti hlim hε2) (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
  have h2 := ENNReal.tendsto_nhds_zero.1 (tendsto_prob_shift (mul_pos hs (Real.exp_pos (-lam)))
    hYi hanti hlim hε2) (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)
  filter_upwards [h1, h2, self_mem_nhdsWithin,
    tendsto_log_inv_nhdsGT.eventually (eventually_gt_atTop 0)] with δ hA1 hA2 hδ hL0
  have hsub : {ω | ε * Real.log δ⁻¹ < |X δ ω - Y δ ω|} ⊆
      ({ω | ¬ (Y (s * δ * Real.exp lam) ω ≤ X δ ω ∧ X δ ω ≤ Y (s * δ * Real.exp (-lam)) ω)} ∪
        {ω | ε / 2 * Real.log δ⁻¹ < |Y (s * Real.exp lam * δ) ω - Y δ ω|}) ∪
        {ω | ε / 2 * Real.log δ⁻¹ < |Y (s * Real.exp (-lam) * δ) ω - Y δ ω|} := by
    intro ω hω
    simp only [mem_union, mem_ofPred_eq] at hω ⊢
    by_contra hcon
    simp only [not_or, not_lt, not_not] at hcon
    obtain ⟨⟨⟨hl, hr⟩, hb1⟩, hb2⟩ := hcon
    rw [show s * δ * Real.exp lam = s * Real.exp lam * δ by ring] at hl
    rw [show s * δ * Real.exp (-lam) = s * Real.exp (-lam) * δ by ring] at hr
    rw [abs_le] at hb1 hb2
    have : |X δ ω - Y δ ω| ≤ ε / 2 * Real.log δ⁻¹ := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith
  calc P {ω | ε * Real.log δ⁻¹ < |X δ ω - Y δ ω|} ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η :=
        add_le_add (add_le_add (hlam δ hδ) hA1) hA2
    _ = e := by
        rw [← ENNReal.ofReal_add hη.le hη.le, ← ENNReal.ofReal_add (by positivity) hη.le,
          show η + η + η = e.toReal by rw [hηdef]; ring, ENNReal.ofReal_toReal het]

end DZZ
end LQGMetric
