/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53YC1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53G6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53H4

/-!
# DZZ Lemma 5.3 part 1: the `(u,v)`-step `l53_uv_far` without the walled Cor 3.9 at `𝕍̃_{u,v}`
(P2-DZZ53YC)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2490–2493 ("we combine the preceding inequality
with Corollary 3.9 and Proposition 3.17"). `l53_uv_far` (S5L53G6) takes the walled Cor 3.9 at the
non-dyadic wall `𝕍̃_{u,v}` as hypothesis `hcor`; that is not available (the walled L3.5 is proved
only for dyadic walls, S3L5W8). Its only use (in `l53_uv_far_large`) is the comparison of the means
`E log D̃_{δ'}(u,v) + (log δ'⁻¹)^{0.95} ≤ E log D̃_{δ̃}(u,v) + L^{0.97}`, `δ' = δ̃ e^{−L^{0.95}}`.
Here this comparison is proved through the dyadic wall `B̄₀ = wsimB₀`, as in P2-DZZ53H's `hd`
(S5L53H2/H4): two tail comparisons through the similarity coupling `θ : B̄₀ → 𝕍̃_{u,v}`
(`l53h_tail`, DZZ lem-scaling-coupling l. 611–624), the walled Cor 3.9 at `B̄₀` (`cor39_boundOn`,
DZZ l. 1235–1244) and the concentration (eq-concentration-2) at `𝕍̃_{u,v}` (`l53_uv_conc2`).

* `l53yc_mean_core`: one point of the intersection of the three good events (law level).
* **`l53yc_mean`**: the comparison of the means for `L^{0.96} ≤ l log 2 ≤ L`, `L ≥ L₀`.
* **`l53_uv_far_large'`**, **`l53_uv_far'`**: `l53_uv_far_large`/`l53_uv_far` without `hcor`
  (the end of the proof of `l53_uv_far_large`, S5L53G6, copied).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **The mean comparison at one pair of scales**, from three good events: the two
concentrations at `𝕍̃_{u,v}`, the Cor 3.9 event at `B̄₀`, and two tail comparisons. -/
theorem l53yc_mean_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {μt μ0 : Ω → Measure ℂ} {u v p₁ p₂ : ℂ} {δt δ' δ₁ δ₂ q₁ q₂ q₃ e : ℝ}
    (hδt : 0 < δt) (hδt1 : δt ≤ 1) (hδ₂ : 0 < δ₂) (h21 : δ₂ ≤ δ₁) (h1 : δ₁ ≤ 1)
    (hc1 : P (conc2Event μt P δ' {u} {v})ᶜ ≤ ENNReal.ofReal q₁)
    (hc2 : P (conc2Event μt P δt {u} {v})ᶜ ≤ ENNReal.ofReal q₂)
    (hfin : ∀ᵐ ω ∂P, lgdDZZ (μt ω) δt u v < ⊤)
    (hc3 : P (cor39Event μ0 δ₁ δ₂ {p₁} {p₂})ᶜ ≤ ENNReal.ofReal q₃)
    (ht1 : ∀ R : ℝ≥0∞, P {ω | R < ((lgdDZZ (μt ω) δ' u v : ℕ∞) : ℝ≥0∞)} ≤
      ENNReal.ofReal e + P {ω | R < ((lgdDZZ (μ0 ω) δ₂ p₁ p₂ : ℕ∞) : ℝ≥0∞)})
    (ht2 : ∀ R : ℝ≥0∞, P {ω | R < ((lgdDZZ (μ0 ω) δ₁ p₁ p₂ : ℕ∞) : ℝ≥0∞)} ≤
      ENNReal.ofReal e + P {ω | R < ((lgdDZZ (μt ω) δt u v : ℕ∞) : ℝ≥0∞)})
    (hq1 : 0 ≤ q₁) (hq2 : 0 ≤ q₂) (hq3 : 0 ≤ q₃) (he : 0 ≤ e)
    (hsum : q₁ + q₂ + q₃ + 2 * e < 1) :
    (∫ ω, logMinLGD (μt ω) δ' {u} {v} ∂P) - Real.log δ'⁻¹ ^ (0.95 : ℝ) - 1 <
      (∫ ω, logMinLGD (μt ω) δt {u} {v} ∂P) + Real.log δt⁻¹ ^ (0.95 : ℝ) +
        Real.log (cor39Fac δ₁ δ₂) := by
  set m' := ∫ ω, logMinLGD (μt ω) δ' {u} {v} ∂P
  set m := ∫ ω, logMinLGD (μt ω) δt {u} {v} ∂P
  set t₁ := m' - Real.log δ'⁻¹ ^ (0.95 : ℝ)
  set t₂ := m + Real.log δt⁻¹ ^ (0.95 : ℝ)
  set F := cor39Fac δ₁ δ₂
  have hF1 : 1 ≤ F := one_le_cor39Fac hδ₂ h21 h1
  have hF0 : 0 < F := by linarith
  have hlogF : 0 ≤ Real.log F := Real.log_nonneg hF1
  have hm0 : 0 ≤ m := integral_nonneg fun _ => Real.log_natCast_nonneg _
  have ht0 : 0 ≤ Real.log δt⁻¹ ^ (0.95 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg ((one_le_inv₀ hδt).2 hδt1)) _
  by_contra hcon
  push Not at hcon
  have ht₂0 : 0 ≤ t₂ := add_nonneg hm0 ht0
  have ht₁ : 0 < t₁ := by linarith
  set G1 := {ω | ENNReal.ofReal (Real.exp (t₁ - 1)) <
    ((lgdDZZ (μ0 ω) δ₂ p₁ p₂ : ℕ∞) : ℝ≥0∞)}
  set G2 := {ω | ENNReal.ofReal (Real.exp t₂) < ((lgdDZZ (μ0 ω) δ₁ p₁ p₂ : ℕ∞) : ℝ≥0∞)}
  -- the three good events are disjoint
  have hsub : G1 ⊆ G2 ∪ (cor39Event μ0 δ₁ δ₂ {p₁} {p₂})ᶜ := by
    intro ω h
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not, G2, mem_ofPred_eq, not_lt] at hc
    obtain ⟨h2, h3⟩ := hc
    simp only [cor39Event, lgdMinSet_singleton, mem_ofPred_eq] at h3
    have h3' : ((lgdDZZ (μ0 ω) δ₂ p₁ p₂ : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp t₂) * ENNReal.ofReal F :=
      h3.trans (mul_le_mul_left h2 _)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le] at h3'
    have hle : Real.exp t₂ * F ≤ Real.exp (t₁ - 1) := by
      rw [← Real.exp_log hF0, ← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    exact absurd (lt_of_lt_of_le h (h3'.trans (ENNReal.ofReal_le_ofReal hle))) (lt_irrefl _)
  -- the tail at `δt` from the concentration
  have hT2 : P {ω | ENNReal.ofReal (Real.exp t₂) <
      ((lgdDZZ (μt ω) δt u v : ℕ∞) : ℝ≥0∞)} ≤ ENNReal.ofReal q₂ := by
    have hnull : P {ω | lgdDZZ (μt ω) δt u v < ⊤}ᶜ = 0 := ae_iff.1 hfin
    refine (measure_mono (t := (conc2Event μt P δt {u} {v})ᶜ ∪
      {ω | lgdDZZ (μt ω) δt u v < ⊤}ᶜ) fun ω hω => ?_).trans
      ((measure_union_le _ _).trans (by rw [hnull, add_zero]; exact hc2))
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq] at hc hω
    obtain ⟨hc2', hlt⟩ := hc
    simp only [conc2Event, mem_ofPred_eq, logMinLGD, lgdMinSet_singleton] at hc2'
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hlt.ne
    rw [← hn] at hc2' hω
    simp only [ENat.toNat_natCast, ENat.toENNReal_coe] at hc2' hω
    have hle : (n : ℝ) ≤ Real.exp t₂ := natCast_le_exp_of_log_le (by
      have := (abs_le.1 hc2').2
      simp only [m, t₂, logMinLGD, lgdMinSet_singleton] at this ⊢; linarith)
    refine absurd hω (not_lt.2 ?_)
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hle
  -- the tail at `δ'` from the concentration
  have hT1 : (univ : Set Ω) ⊆ {ω | ENNReal.ofReal (Real.exp (t₁ - 1)) <
      ((lgdDZZ (μt ω) δ' u v : ℕ∞) : ℝ≥0∞)} ∪ (conc2Event μt P δ' {u} {v})ᶜ := by
    intro ω _
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq, not_lt] at hc
    obtain ⟨hle, hc1'⟩ := hc
    simp only [conc2Event, mem_ofPred_eq, logMinLGD, lgdMinSet_singleton] at hc1'
    have hlo : t₁ ≤ Real.log ((lgdDZZ (μt ω) δ' u v).toNat : ℝ) := by
      have := (abs_le.1 hc1').1
      simp only [t₁, m', logMinLGD, lgdMinSet_singleton] at this ⊢; linarith
    rcases eq_top_or_lt_top (lgdDZZ (μt ω) δ' u v) with htop | hfin'
    · rw [htop, ENat.toENNReal_top] at hle
      exact ENNReal.ofReal_ne_top (top_le_iff.1 hle)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin'.ne
    rw [← hn] at hle hlo
    simp only [ENat.toNat_natCast, ENat.toENNReal_coe] at hle hlo
    have hn0 : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp at hlo; linarith
      · exact_mod_cast hn
    have hlt : Real.exp (t₁ - 1) < n := by
      rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.2 (by linarith)
    rw [← ENNReal.ofReal_natCast] at hle
    exact absurd ((ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 hle) (not_le.2 hlt)
  have key : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (q₁ + q₂ + q₃ + 2 * e) := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ _ := (measure_mono hT1).trans (measure_union_le _ _)
      _ ≤ (ENNReal.ofReal e + P G1) + ENNReal.ofReal q₁ := add_le_add (ht1 _) hc1
      _ ≤ (ENNReal.ofReal e + ((ENNReal.ofReal e + ENNReal.ofReal q₂) + ENNReal.ofReal q₃)) +
          ENNReal.ofReal q₁ := by
          gcongr
          exact (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add ((ht2 _).trans (add_le_add le_rfl hT2)) hc3))
      _ = ENNReal.ofReal (q₁ + q₂ + q₃ + 2 * e) := by
          rw [← ENNReal.ofReal_add he hq2, ← ENNReal.ofReal_add (by positivity) hq3,
            ← ENNReal.ofReal_add he (by positivity), ← ENNReal.ofReal_add (by positivity) hq1]
          congr 1; ring
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  linarith

/-- `L^a ≤ L^b / D` eventually, for `a < b`, `D > 0` -/
lemma l53yc_rpow_ev {a b D : ℝ} (hab : a < b) (hD : 0 < D) :
    ∀ᶠ L : ℝ in atTop, D * L ^ a ≤ L ^ b := by
  have h := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < b - a)).eventually (eventually_ge_atTop D)
  filter_upwards [h, eventually_gt_atTop 0] with L hL hL0
  have : L ^ b = L ^ a * L ^ (b - a) := by rw [← Real.rpow_add hL0]; ring_nf
  rw [this, mul_comm D]
  exact mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hL0.le _)

/-- **The comparison of the means** (the use of Cor 3.9 in DZZ l. 2490–2493), through `B̄₀`:
for `L^{0.96} ≤ l log 2 ≤ L` and `δ' = 2^{-l} e^{−L^{0.95}}`,
`E log D̃_{δ'}(u,v) + (log δ'⁻¹)^{0.95} ≤ E log D̃_{2^{-l}}(u,v) + L^{0.97}`. -/
theorem l53yc_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ξ : ℝ} (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ)
    (hξ4 : ξ ≤ 1 / 4) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (h2ξ : 2 * ξ ≤ dist u v) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ l : ℕ, L ^ (0.96 : ℝ) ≤ (l : ℝ) * Real.log 2 →
      (l : ℝ) * Real.log 2 ≤ L →
      (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω))
          ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) {u} {v} ∂P) +
        Real.log ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ))))⁻¹ ^ (0.95 : ℝ) ≤
      (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
        L ^ (0.97 : ℝ) := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨δc, hδc, hconc⟩ := l53_uv_conc2 h317 hξ4 hu hv huv h2ξ hξ
  have hCM := dzzCMc_pos γ
  have h32 := dzz_prop32UOn_of hW hγ hγ2 (ξ := 1 / 16) (ξd := 0) (by norm_num) hCM
    (l32BallCoverOn_inside_dzzMuIn hW hγ hγ2 wsimB₀)
    (l32UpperCrossOn_dzzMuIn hW hγ hγ2 wsimB₀ (by norm_num) hCM)
    (fun _ h => dzz_lemma35UOn_wall hW hγ hγ2 wsimB₀ (by norm_num) h)
  obtain ⟨c₃, hc₃, δ₃, hδ₃, -, hcor⟩ := cor39_boundOn le_rfl h32
    (dzz_lemma35UOn_wall hW hγ hγ2 wsimB₀ (by norm_num) hCM)
  obtain ⟨C, hC, ht⟩ := l53h_tail hW hγ hγ2 (l53hA_ne huv) (l53hA_norm_le hu hv)
    (by rw [l53h_sim_image huv]; exact tildeBox_subset_dzzVXi hu hv huv)
  set α := ‖l53hA u v‖ with hαdef
  have hα0 : 0 < α := l53hA_norm_pos huv
  have hα1 : α ≤ 1 := l53hA_norm_le hu hv
  set A := Real.log α⁻¹ with hA
  have hA0 : 0 ≤ A := Real.log_nonneg ((one_le_inv₀ hα0).2 hα1)
  -- eventual conditions
  have tA : Tendsto (fun L : ℝ => L ^ (0.96 : ℝ) / 2 - A) atTop atTop :=
    tendsto_atTop_add_const_right _ (-A)
      ((tendsto_rpow_atTop (by norm_num)).atTop_div_const two_pos)
  have ev1 : ∀ᶠ L : ℝ in atTop, Real.exp (-(L ^ (0.96 : ℝ))) < δc :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop (by norm_num))).eventually
      (gt_mem_nhds hδc))
  have ev2 : ∀ᶠ L : ℝ in atTop, Real.exp (-(L ^ (0.96 : ℝ) / 2 - A)) < min δ₃ 1 :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp tA).eventually
      (gt_mem_nhds (lt_min hδ₃ one_pos)))
  have ev3 : ∀ᶠ L : ℝ in atTop, Real.exp (-((L ^ (0.95 : ℝ)) ^ (0.7 : ℝ))) +
      Real.exp (-((L ^ (0.96 : ℝ)) ^ (0.7 : ℝ))) +
      3 * Real.exp (-(c₃ * (L ^ (0.96 : ℝ) / 2 - A))) +
      2 * (C * Real.exp (-(L ^ (0.6 : ℝ)) ^ 2 / C)) < 1 := by
    have t1 : Tendsto (fun L : ℝ => (L ^ (0.95 : ℝ)) ^ (0.7 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp (tendsto_rpow_atTop (by norm_num))
    have t2 : Tendsto (fun L : ℝ => (L ^ (0.96 : ℝ)) ^ (0.7 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp (tendsto_rpow_atTop (by norm_num))
    have t3 : Tendsto (fun L : ℝ => c₃ * (L ^ (0.96 : ℝ) / 2 - A)) atTop atTop :=
      tA.const_mul_atTop hc₃
    have t4 : Tendsto (fun L : ℝ => (L ^ (0.6 : ℝ)) ^ 2 / C) atTop atTop :=
      ((tendsto_pow_atTop two_ne_zero).comp (tendsto_rpow_atTop (by norm_num))).atTop_div_const hC
    have e : Tendsto (fun L : ℝ => Real.exp (-((L ^ (0.95 : ℝ)) ^ (0.7 : ℝ))) +
        Real.exp (-((L ^ (0.96 : ℝ)) ^ (0.7 : ℝ))) +
        3 * Real.exp (-(c₃ * (L ^ (0.96 : ℝ) / 2 - A))) +
        2 * (C * Real.exp (-((L ^ (0.6 : ℝ)) ^ 2 / C)))) atTop (𝓝 (0 + 0 + 3 * 0 + 2 * (C * 0))) :=
      (((Real.tendsto_exp_neg_atTop_nhds_zero.comp t1).add
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp t2)).add
        ((Real.tendsto_exp_neg_atTop_nhds_zero.comp t3).const_mul 3)).add
        (((Real.tendsto_exp_neg_atTop_nhds_zero.comp t4).const_mul C).const_mul 2)
    simp only [add_zero, mul_zero] at e
    filter_upwards [e.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with L hL
    simpa only [neg_div] using hL
  have ev5 : ∀ᶠ L : ℝ in atTop, 2 * L ^ (0.6 : ℝ) ≤ L ^ (0.96 : ℝ) :=
    l53yc_rpow_ev (by norm_num) two_pos
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (ev1.and (ev2.and (ev3.and
    ((l53yc_rpow_ev (by norm_num : (0.95 : ℝ) < 0.97) (by norm_num : (0 : ℝ) < 30)).and
      (ev5.and (eventually_ge_atTop 1))))))
  refine ⟨L₀, fun L hL l hl1 hl2 => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, hL1⟩ := hL₀ L hL
  have hL0 : 0 ≤ L := by linarith
  set y : ℝ := (l : ℝ) * Real.log 2 with hy
  set δt : ℝ := (2 : ℝ)⁻¹ ^ l with hδt
  set δ' : ℝ := δt * Real.exp (-(L ^ (0.95 : ℝ))) with hδ'
  set lam : ℝ := L ^ (0.6 : ℝ) with hlam
  have hδt0 : 0 < δt := by positivity
  have hδ'0 : 0 < δ' := by positivity
  have hyt : Real.log δt⁻¹ = y := l53_log_two_pow l
  have hδt_eq : δt = Real.exp (-y) := by
    rw [← hyt, Real.log_inv, neg_neg, Real.exp_log hδt0]
  have h96 : 1 ≤ L ^ (0.96 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h95 : 1 ≤ L ^ (0.95 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hy1 : 1 ≤ y := h96.trans hl1
  set x : ℝ := Real.log δ'⁻¹ with hxdef
  have hx : x = y + L ^ (0.95 : ℝ) := by
    rw [hxdef, hδ', mul_inv, Real.log_mul (by positivity) (by positivity), hyt, ← Real.exp_neg,
      neg_neg, Real.log_exp]
  have hδ'_eq : δ' = Real.exp (-x) := by
    rw [hxdef, Real.log_inv, neg_neg, Real.exp_log hδ'0]
  have hαe : α⁻¹ = Real.exp A := by rw [hA, Real.exp_log (inv_pos.2 hα0)]
  set δ₁ : ℝ := δt * Real.exp lam / α with hδ₁
  set δ₂ : ℝ := δ' * Real.exp (-lam) / α with hδ₂
  have hδ₁e : δ₁ = Real.exp (-(y - lam - A)) := by
    rw [hδ₁, div_eq_mul_inv, hαe, hδt_eq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hδ₂e : δ₂ = Real.exp (-(x + lam - A)) := by
    rw [hδ₂, div_eq_mul_inv, hαe, hδ'_eq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hlam0 : 0 ≤ lam := by positivity
  have hb₁ : L ^ (0.96 : ℝ) / 2 - A ≤ y - lam - A := by linarith
  have hδ₁le : δ₁ ≤ Real.exp (-(L ^ (0.96 : ℝ) / 2 - A)) := by
    rw [hδ₁e]; exact Real.exp_le_exp.2 (by linarith)
  have hδ₁0 : 0 < δ₁ := by positivity
  have hδ₂0 : 0 < δ₂ := by positivity
  have hδ₁1 : δ₁ ≤ 1 := hδ₁le.trans (e2.le.trans (min_le_right _ _))
  have hδ₁3 : δ₁ < δ₃ := hδ₁le.trans_lt (e2.trans_le (min_le_left _ _))
  have hδ₂₁ : δ₂ < δ₁ := by
    rw [hδ₁e, hδ₂e]; exact Real.exp_lt_exp.2 (by linarith)
  have hlt₁ : δt < δc := by
    rw [hδt_eq]; exact lt_of_le_of_lt (Real.exp_le_exp.2 (by linarith)) e1
  have hδ't : δ' < δt := mul_lt_of_lt_one_right hδt0
    (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith))
  -- the inputs of the core
  have hc1 := hconc δ' ⟨hδ'0, hδ't.trans hlt₁⟩
  have hc2 := hconc δt ⟨hδt0, hlt₁⟩
  have hc3 := hcor δ₁ ⟨hδ₁0, hδ₁3⟩ δ₂ ⟨hδ₂0, hδ₂₁⟩ _ _ (l53h_admB₀ δ₁)
  have hfin := ae_lgd_tilde_lt_top (P := P) hW hγ hγ2 hu hv huv hδt0
  have ht1 : ∀ R : ℝ≥0∞,
      P {ω | R < ((lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ' u v : ℕ∞) : ℝ≥0∞)} ≤
      ENNReal.ofReal (C * Real.exp (-lam ^ 2 / C)) +
        P {ω | R < ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δ₂ ⟨5 / 16, 3 / 8⟩
          ⟨7 / 16, 3 / 8⟩ : ℕ∞) : ℝ≥0∞)} := by
    intro R
    have s := (ht lam hlam0 _ l53h_p₁_mem _ l53h_p₂_mem δ₂ hδ₂0 R).1
    have e : α * δ₂ * Real.exp lam = δ' := by
      rw [hδ₂]; field_simp; first | (rw [← Real.exp_add]; simp) | (rw [mul_assoc, ← Real.exp_add]; simp)
    rw [e, l53h_sim_image huv, l53h_sim_p₁, l53h_sim_p₂] at s
    exact s
  have ht2 : ∀ R : ℝ≥0∞,
      P {ω | R < ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δ₁ ⟨5 / 16, 3 / 8⟩
          ⟨7 / 16, 3 / 8⟩ : ℕ∞) : ℝ≥0∞)} ≤
      ENNReal.ofReal (C * Real.exp (-lam ^ 2 / C)) +
        P {ω | R < ((lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δt u v : ℕ∞) : ℝ≥0∞)} := by
    intro R
    have s := (ht lam hlam0 _ l53h_p₁_mem _ l53h_p₂_mem δ₁ hδ₁0 R).2
    have e : α * δ₁ * Real.exp (-lam) = δt := by
      rw [hδ₁]; field_simp; first | (rw [← Real.exp_add]; simp) | (rw [mul_assoc, ← Real.exp_add]; simp)
    rw [e, l53h_sim_image huv, l53h_sim_p₁, l53h_sim_p₂] at s
    exact s
  -- the probabilities
  have hq1 : Real.exp (-(x ^ (0.7 : ℝ))) ≤ Real.exp (-((L ^ (0.95 : ℝ)) ^ (0.7 : ℝ))) :=
    Real.exp_le_exp.2 (neg_le_neg (Real.rpow_le_rpow (by positivity) (by rw [hx]; linarith)
      (by norm_num)))
  have hq2 : Real.exp (-(Real.log δt⁻¹ ^ (0.7 : ℝ))) ≤
      Real.exp (-((L ^ (0.96 : ℝ)) ^ (0.7 : ℝ))) := by
    rw [hyt]
    exact Real.exp_le_exp.2 (neg_le_neg (Real.rpow_le_rpow (by positivity) hl1 (by norm_num)))
  have hq3 : 3 * δ₁ ^ c₃ ≤ 3 * Real.exp (-(c₃ * (L ^ (0.96 : ℝ) / 2 - A))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc δ₁ ^ c₃ ≤ Real.exp (-(L ^ (0.96 : ℝ) / 2 - A)) ^ c₃ :=
          Real.rpow_le_rpow hδ₁0.le hδ₁le hc₃.le
      _ = _ := by rw [← Real.exp_mul]; ring_nf
  have hsum : Real.exp (-(x ^ (0.7 : ℝ))) + Real.exp (-(Real.log δt⁻¹ ^ (0.7 : ℝ))) +
      3 * δ₁ ^ c₃ + 2 * (C * Real.exp (-lam ^ 2 / C)) < 1 := by linarith
  have hδt1 : δt ≤ 1 := by rw [hδt_eq]; exact Real.exp_le_one_iff.2 (by linarith)
  have core := l53yc_mean_core (P := P)
    (μt := fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω))
    (μ0 := fun ω => dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) hδt0 hδt1
    hδ₂0 hδ₂₁.le hδ₁1 hc1 hc2 hfin hc3 ht1 ht2 (by positivity) (by positivity) (by positivity)
    (by positivity) hsum
  beta_reduce at core
  -- the exponents
  rw [wsim_log_cor39Fac hδ₁0 hδ₂0, hyt, ← hxdef] at core
  have hl1' : Real.log δ₁⁻¹ = y - lam - A := by
    rw [hδ₁e, Real.log_inv, Real.log_exp, neg_neg]
  have hl2' : Real.log δ₂⁻¹ = x + lam - A := by
    rw [hδ₂e, Real.log_inv, Real.log_exp, neg_neg]
  rw [hl1', hl2'] at core
  have hb1 : 0 ≤ y - lam - A := by
    have h := hδ₁1; rw [hδ₁e, Real.exp_le_one_iff] at h; linarith
  have hb2 : 0 ≤ x + lam - A := by rw [hx]; linarith
  have hxle : x ≤ 2 * L := by
    rw [hx]
    have : L ^ (0.95 : ℝ) ≤ L := Real.rpow_le_self_of_one_le hL1 (by norm_num)
    linarith
  have p1 : y ^ (0.95 : ℝ) ≤ L ^ (0.95 : ℝ) := Real.rpow_le_rpow (by positivity) hl2 (by norm_num)
  have p2 : (y - lam - A) ^ (0.9 : ℝ) ≤ L ^ (0.95 : ℝ) :=
    (Real.rpow_le_rpow hb1 (by linarith) (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have p3 : (y - lam - A) ^ (0.8 : ℝ) ≤ L ^ (0.95 : ℝ) :=
    (Real.rpow_le_rpow hb1 (by linarith) (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have h3pow : ∀ z p : ℝ, 0 ≤ z → 0 ≤ p → p ≤ 1 → (3 * z) ^ p ≤ 3 * z ^ p := fun z p hz hp hp1 => by
    rw [Real.mul_rpow (by norm_num) hz]
    gcongr
    calc (3 : ℝ) ^ p ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
      _ = 3 := Real.rpow_one 3
  have hlamL : lam ≤ L := Real.rpow_le_self_of_one_le hL1 (by norm_num)
  have p4 : (x + lam - A) ^ (0.9 : ℝ) ≤ 3 * L ^ (0.95 : ℝ) :=
    calc (x + lam - A) ^ (0.9 : ℝ) ≤ (3 * L) ^ (0.9 : ℝ) :=
          Real.rpow_le_rpow hb2 (by linarith) (by norm_num)
      _ ≤ 3 * L ^ (0.9 : ℝ) := h3pow L _ hL0 (by norm_num) (by norm_num)
      _ ≤ 3 * L ^ (0.95 : ℝ) := by
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
            (by norm_num)
  have p5 : x ^ (0.95 : ℝ) ≤ 3 * L ^ (0.95 : ℝ) :=
    (Real.rpow_le_rpow (by rw [hx]; linarith) (by linarith) (by norm_num)).trans
      (h3pow L _ hL0 (by norm_num) (by norm_num))
  have p6 : lam ≤ L ^ (0.95 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  linarith

/-- **`l53_uv_far_large` without `hcor`** (regime `l log 2 ≥ L^{0.96}`): the mean comparison
`l53yc_mean` and the concentration at `δ'` (the last step of `l53_uv_far_large`, copied). -/
theorem l53_uv_far_large' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ξ : ℝ} (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ)
    (hξ4 : ξ ≤ 1 / 4) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (h2ξ : 2 * ξ ≤ dist u v) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ l : ℕ, L ^ (0.96 : ℝ) ≤ (l : ℝ) * Real.log 2 →
      (l : ℝ) * Real.log 2 ≤ L →
      P {ω | (∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
          ∂P) + L ^ (0.97 : ℝ) <
        logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω))
          ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) {u} {v}} ≤
        ENNReal.ofReal (((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) := by
  obtain ⟨δc, hδc, hconc⟩ := l53_uv_conc2 h317 hξ4 hu hv huv h2ξ hξ
  obtain ⟨L₁, hL₁⟩ := l53yc_mean hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ
  have ev1 : ∀ᶠ L : ℝ in atTop, Real.exp (-(L ^ (0.96 : ℝ))) < δc :=
    ((Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop (by norm_num))).eventually
      (gt_mem_nhds hδc))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (ev1.and (l53_K4_of_rpow.and ((eventually_ge_atTop L₁).and (eventually_ge_atTop 1))))
  refine ⟨L₀, fun L hL l hl1 hl2 => ?_⟩
  obtain ⟨e1, e4, hLL, hL1⟩ := hL₀ L hL
  have hmean := hL₁ L hLL l hl1 hl2
  set δt : ℝ := (2 : ℝ)⁻¹ ^ l with hδt
  set δ' : ℝ := δt * Real.exp (-(L ^ (0.95 : ℝ))) with hδ'
  have hδt0 : 0 < δt := by positivity
  have hyt : Real.log δt⁻¹ = (l : ℝ) * Real.log 2 := l53_log_two_pow l
  have hδt_eq : δt = Real.exp (-((l : ℝ) * Real.log 2)) := by
    rw [← hyt, Real.log_inv, neg_neg, Real.exp_log hδt0]
  have hlt₁ : δt < δc := by
    rw [hδt_eq]; exact lt_of_le_of_lt (Real.exp_le_exp.2 (by linarith)) e1
  have hδ't : δ' < δt := mul_lt_of_lt_one_right hδt0
    (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by
      have : 1 ≤ L ^ (0.95 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith))
  have hxge : L ^ (0.95 : ℝ) ≤ Real.log δ'⁻¹ := by
    rw [hδ', mul_inv, Real.log_mul (by positivity) (by positivity), hyt, ← Real.exp_neg,
      neg_neg, Real.log_exp]
    have : 0 ≤ (l : ℝ) * Real.log 2 := by positivity
    linarith
  have hG1 := hconc δ' ⟨by positivity, hδ't.trans hlt₁⟩
  refine le_trans (measure_mono fun ω hω => ?_)
    (hG1.trans (ENNReal.ofReal_le_ofReal (e4 _ hxge)))
  simp only [mem_ofPred_eq] at hω
  simp only [conc2Event, mem_compl_iff, mem_ofPred_eq, not_le]
  have := lt_of_le_of_lt hmean hω
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

/-- **`l53_uv_far` without `hcor`** (DZZ l. 2490–2493): all `l` with `l log 2 ≤ L`. -/
theorem l53_uv_far' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {ξ : ℝ} (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) (hξ : 0 < ξ)
    (hξ4 : ξ ≤ 1 / 4) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (h2ξ : 2 * ξ ≤ dist u v) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ l : ℕ, (l : ℝ) * Real.log 2 ≤ L →
      P {ω | (∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v}
          ∂P) + L ^ (0.97 : ℝ) <
        logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω))
          ((2 : ℝ)⁻¹ ^ l * Real.exp (-(L ^ (0.95 : ℝ)))) {u} {v}} ≤
        ENNReal.ofReal (((2 : ℝ) ^ ⌊L ^ (0.51 : ℝ)⌋₊)⁻¹ ^ 4) := by
  obtain ⟨L₁, h₁⟩ := l53_uv_far_small hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ
  obtain ⟨L₂, h₂⟩ := l53_uv_far_large' hW hγ hγ2 h317 hξ hξ4 hu hv huv h2ξ
  refine ⟨max L₁ L₂, fun L hL l hl => ?_⟩
  rcases le_total ((l : ℝ) * Real.log 2) (L ^ (0.96 : ℝ)) with hs | hs
  · exact h₁ L ((le_max_left _ _).trans hL) l hs
  · exact h₂ L ((le_max_right _ _).trans hL) l hs hl

end DZZ
end LQGMetric
