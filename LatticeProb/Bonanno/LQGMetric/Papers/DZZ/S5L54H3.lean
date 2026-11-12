/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54H3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54H2

/-!
# D117 P-54C (5): `cfg_whp`, the contradiction of DZZ L5.4 (P2-DZZ54C)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2553–2568; see S5L54H2 for the plan.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the final arithmetic of the contradiction -/
lemma cfg_arith {χ ι δ : ℝ} (hι : 0 < ι) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsm : δ ^ (ι / 4) < 1 / 4)
    (h : δ ^ (-(χ - ι / 4)) ≤ 2 * δ ^ (-(χ - ι / 2)) + 2 * δ ^ (-(χ - ι))) : False := by
  have e1 : δ ^ (-(χ - ι / 2)) = δ ^ (-(χ - ι / 4)) * δ ^ (ι / 4) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have e2 : δ ^ (-(χ - ι)) ≤ δ ^ (-(χ - ι / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)
  have hp : 0 < δ ^ (-(χ - ι / 4)) := Real.rpow_pos_of_pos hδ _
  rw [e1] at e2 h
  nlinarith

/-- **DZZ (eq-point-to-segment) in the reflection configuration, w.p. → 1, uniformly in the
segment** (DZZ l. 2553–2568). -/
theorem cfg_whp {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {χ ι κ ξ : ℝ} (hι : 0 < ι) (hι1 : ι < 1) (hκ : 0 < κ)
    (hκχ : 2 * ι ≤ κ * χ) (hκ1 : κ < 1) (hκξ : 2 * κ ≤ ξ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80)
    (hL53 : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317 : DZZProp317In P (fun ω => dzzWall (tildeBox u₅₄ v₅₄) (dzzMuIn γ W ω))
      (tildeBox u₅₄ v₅₄) ξ)
    (h317R : DZZProp317In P (fun ω => dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω))
      (tildeBox ringU₀ ringV₀) ξ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ s t : ℝ, SegC κ δ s t →
      P {ω | logMinLGD (dzzWall K₅₄ (dzzMuIn γ W ω)) δ {u₅₄} (vSeg s t) <
        (χ - ι) * Real.log δ⁻¹} ≤ ENNReal.ofReal η := by
  intro η hη
  haveI := hW.isProbabilityMeasure
  -- the ring crossings
  have hKR : tildeBox ringU₀ ringV₀ ⊆ dzzVXi ξ := fun z hz => by
    have h := tildeBox_subset_dzzVXi ringU₀_mem_dzzVbar ringV₀_mem_dzzVbar ringU₀_ne_ringV₀ hz
    exact ⟨h.1, le_trans (by linarith) h.2⟩
  obtain ⟨f, hf, hring⟩ := ring_pairs_whp hW hγ hγ2 hι hκ hκχ hκ1 hξ hξ1
    (dzzSimCoupleScale_of hγ hγ2 hξ (by linarith) (isClosed_tildeBox _ _) hKR) hL53 h317R
    (eventually_nhdsWithin_of_forall fun _ hδ => ae_lgd_tilde_lt_top hW hγ hγ2
      ringU₀_mem_dzzVbar ringV₀_mem_dzzVbar ringU₀_ne_ringV₀ hδ)
  -- the points
  have hd₀ : 2 * ξ ≤ dist u₅₄ v₅₄ := by rw [dist_u₅₄_v₅₄]; linarith
  have huK : u₅₄ ∈ kXi K₅₄ ξ := by
    rw [← tildeBox_u₅₄_v₅₄]; exact mem_kXi_tildeBox_left u₅₄_ne_v₅₄ hd₀
  have hvK : v₅₄ ∈ kXi K₅₄ ξ := by
    rw [← tildeBox_u₅₄_v₅₄]; exact mem_kXi_tildeBox_right u₅₄_ne_v₅₄ hd₀
  have huξ : u₅₄ ∈ dzzVXi ξ := mem_dzzVXi_of_near (a := 1 / 40) (by norm_num [u₅₄])
    (by norm_num [u₅₄]) (by linarith) hξ.le
  have hvξ : v₅₄ ∈ dzzVXi ξ := mem_dzzVXi_of_near (a := 1 / 40) (by norm_num [v₅₄])
    (by norm_num [v₅₄]) (by linarith) hξ.le
  have hcξ : c₅₄ ∈ dzzVXi ξ := mem_dzzVXi_of_near (a := 1 / 40) (by norm_num [c₅₄])
    (by norm_num [c₅₄]) (by linarith) hξ.le
  have hcK : c₅₄ ∈ kXi K₅₄ ξ := mem_kXi_sqBox (by simp only [c₅₄]; norm_num; linarith)
    (by simp only [c₅₄]; norm_num; linarith)
  have hdc : ξ ≤ dist u₅₄ c₅₄ := by
    rw [dist_eq_norm]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    simp only [Complex.sub_re, u₅₄, c₅₄]; norm_num; linarith
  rw [tildeBox_u₅₄_v₅₄] at h317
  -- the lower bound for `D̃(u₅₄, v₅₄)`
  have hT := dzz_lgd_lower_whpIn h317 (isXiAdmissible_const_singleton huξ hvξ (by linarith))
    (fun _ _ => ⟨singleton_subset_iff.2 huK, singleton_subset_iff.2 hvK⟩)
    (by simpa only [tildeBox_u₅₄_v₅₄] using
      hL53 u₅₄ u₅₄_mem_dzzVbar v₅₄ v₅₄_mem_dzzVbar u₅₄_ne_v₅₄) (ι := ι / 4) (by positivity)
  simp only [lgdMinSet_singleton] at hT
  -- the contradiction
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  classical
  set A : ℝ → ℝ → ℝ → Set Ω := fun δ s t => {ω | logMinLGD (dzzWall K₅₄ (dzzMuIn γ W ω)) δ
    {u₅₄} (vSeg s t) < (χ - ι) * Real.log δ⁻¹} with hAdef
  set Bad : ℝ → Prop := fun δ => ¬ ∀ s t : ℝ, SegC κ δ s t → P (A δ s t) ≤ ENNReal.ofReal η
    with hBad
  have hch : ∀ δ, ∃ p : ℝ × ℝ, Bad δ → SegC κ δ p.1 p.2 ∧ ENNReal.ofReal η < P (A δ p.1 p.2) := by
    intro δ
    by_cases h : Bad δ
    · have h' := h
      simp only [hBad, not_forall, not_le] at h'
      obtain ⟨s, t, h1, h2⟩ := h'
      exact ⟨(s, t), fun _ => ⟨h1, h2⟩⟩
    · exact ⟨(0, 0), fun h' => absurd h' h⟩
  choose pf hpf using hch
  set Lf : ℝ → Set ℂ := fun δ => if Bad δ then vSeg (pf δ).1 (pf δ).2 else {c₅₄} with hLfdef
  have hLf : ∀ δ ∈ Ioo (0 : ℝ) 1, Lf δ ⊆ dzzVXi ξ ∧ IsXiAdmissibleSet ξ δ (Lf δ) ∧
      Lf δ ⊆ kXi K₅₄ ξ ∧ ∀ b ∈ Lf δ, ξ ≤ dist u₅₄ b := by
    intro δ hδ
    by_cases hb : Bad δ
    · obtain ⟨⟨hs, ht, h2κ, -⟩, -⟩ := hpf δ hb
      have hst : (pf δ).1 ≤ (pf δ).2 := by
        have := Real.rpow_pos_of_pos hδ.1 (2 * κ); linarith
      have hP := vSeg_props hξ.le hξ1 hs ht
      simp only [hLfdef, if_pos hb]
      refine ⟨fun z hz => (hP z hz).1, Or.inr ⟨(vSeg_adm hs ht hst).1, ?_⟩,
        fun z hz => (hP z hz).2.1, fun z hz => (hP z hz).2.2⟩
      refine le_trans ?_ ((le_trans h2κ (vSeg_adm hs ht hst).2))
      exact Real.rpow_le_rpow_of_exponent_ge hδ.1 hδ.2.le hκξ
    · simp only [hLfdef, if_neg hb]
      exact ⟨singleton_subset_iff.2 hcξ, Or.inl ⟨_, rfl⟩, singleton_subset_iff.2 hcK,
        fun b hb' => by rw [mem_singleton_iff.1 hb']; exact hdc⟩
  have hAB : IsXiAdmissible ξ (fun _ => {u₅₄}) Lf :=
    ⟨fun _ _ => singleton_subset_iff.2 huξ, fun δ hδ => (hLf δ hδ).1, fun _ _ => Or.inl ⟨_, rfl⟩,
      fun δ hδ => (hLf δ hδ).2.1, fun δ hδ a ha b hb => by
        rw [mem_singleton_iff.1 ha]; exact (hLf δ hδ).2.2.2 b hb⟩
  obtain ⟨c3, hc3, h317'⟩ := h317
  obtain ⟨δ₀, hδ₀, hconc⟩ := (h317' _ _ hAB (fun δ hδ =>
    ⟨singleton_subset_iff.2 huK, (hLf δ hδ).2.2.1⟩)).1 (ι / 4) ⟨by positivity, by linarith⟩
  -- the eventual smallness
  set e := c3 * (ι / 4) ^ 2 with he
  have he0 : 0 < e := by positivity
  have hlim : Tendsto (fun δ => 2 * ENNReal.ofReal (δ ^ e) + f δ +
      P {ω | ¬ ENNReal.ofReal (δ ^ (-(χ - ι / 4))) ≤
        ((lgdDZZ (dzzWall K₅₄ (dzzMuIn γ W ω)) δ u₅₄ v₅₄ : ℕ∞) : ℝ≥0∞)}) (𝓝[>] 0) (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_rpow_zero he0)
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    have := (h1.add hf).add hT
    simpa using this
  have ev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 2 * ENNReal.ofReal (δ ^ e) + f δ +
      P {ω | ¬ ENNReal.ofReal (δ ^ (-(χ - ι / 4))) ≤
        ((lgdDZZ (dzzWall K₅₄ (dzzMuIn γ W ω)) δ u₅₄ v₅₄ : ℕ∞) : ℝ≥0∞)} < 1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (δ ^ e) < ENNReal.ofReal η :=
    (tendsto_order.1 (tendsto_ofReal_rpow_zero he0)).2 _ (ENNReal.ofReal_pos.2 hη)
  have ev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ (ι / 4) < 1 / 4 :=
    tendsto_rpow_nhdsGT_zero (by positivity) (Iio_mem_nhds (by norm_num))
  obtain ⟨δ, hbad, hev⟩ := (hcon.and_eventually (((((eventually_Ioo_nhdsGT hδ₀).and
    ev1).and ev2).and ev3).and hring)).exists
  obtain ⟨⟨⟨⟨hδ, h1⟩, h2⟩, h3⟩, h4⟩ := hev
  have hb : Bad δ := hbad
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ < 1 := hδ.2.trans_le (min_le_right _ _)
  have hδδ₀ : δ < δ₀ := hδ.2.trans_le (min_le_left _ _)
  obtain ⟨hseg, hA⟩ := hpf δ hb
  obtain ⟨hs, ht, h2κ, hκ'⟩ := hseg
  have hLδ : Lf δ = vSeg (pf δ).1 (pf δ).2 := by simp only [hLfdef, if_pos hb]
  set s := (pf δ).1 with hsdef
  set t := (pf δ).2 with htdef
  have hst : s ≤ t := by have := Real.rpow_pos_of_pos hδ0 (2 * κ); linarith
  have hℓ0 : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ0).2 hδ1)
  set ν : Ω → Measure ℂ := fun ω => dzzWall K₅₄ (dzzMuIn γ W ω) with hν
  set X : Ω → ℝ := fun ω => logMinLGD (ν ω) δ {u₅₄} (vSeg s t) with hX
  set E := ∫ ω, X ω ∂P with hEdef
  set Cn := conc1Event ν P δ (ι / 4) {u₅₄} (vSeg s t) with hCndef
  have hCn : P Cnᶜ ≤ ENNReal.ofReal (δ ^ e) := by
    have := hconc δ ⟨hδ0, hδδ₀⟩
    simp only [hLδ] at this
    exact this
  -- the mean is small
  have hE : E < (χ - 3 * ι / 4) * Real.log δ⁻¹ := by
    by_contra hE
    push Not at hE
    have hsub : A δ s t ⊆ Cnᶜ := by
      intro ω hω hc
      simp only [hAdef, mem_setOf_eq] at hω
      simp only [hCndef, conc1Event, mem_setOf_eq] at hc
      have := (abs_le.1 hc).1
      simp only [hX, hEdef] at hE this
      nlinarith
    exact absurd (hA.trans_le ((measure_mono hsub).trans hCn)) (not_lt.2 h2.le)
  -- the bad events
  set cL : ℂ := ⟨1 / 2, (s + t) / 2⟩ with hcL
  have hcLr : |cL.re - 1 / 2| ≤ 1 / 20 := by simp [cL]
  have hcLi : |cL.im - 1 / 2| ≤ 1 / 40 := by
    simp only [cL]; rw [abs_le]; constructor <;> linarith
  set B1 := Cnᶜ
  set B2 := {ω | ¬ logMinLGD (ν ω) δ {v₅₄} (vSeg s t) ≤ (χ - ι / 2) * Real.log δ⁻¹}
  set B3 := {ω | ¬ RingOK (dzzMuIn γ W ω) δ κ (χ - ι) cL}
  set B4 := {ω | ¬ ENNReal.ofReal (δ ^ (-(χ - ι / 4))) ≤
    ((lgdDZZ (dzzWall K₅₄ (dzzMuIn γ W ω)) δ u₅₄ v₅₄ : ℕ∞) : ℝ≥0∞)} with hB4
  set B5 := {ω | ¬ lgdMinSet (ν ω) δ {u₅₄} (vSeg s t) < ⊤}
  set B6 := {ω | ¬ lgdMinSet (ν ω) δ {v₅₄} (vSeg s t) < ⊤}
  have hre : ∀ x ∈ vSeg s t, x.re = 1 / 2 := fun x hx => (mem_vSeg.1 hx).1
  have hB2 : P B2 ≤ P B1 := by
    have e := prob_mirror_eq hW hγ hγ2 δ hre
      {n : ℕ∞ | ¬ Real.log (n.toNat : ℝ) ≤ (χ - ι / 2) * Real.log δ⁻¹}
    have e' : P B2 = P {ω | ¬ X ω ≤ (χ - ι / 2) * Real.log δ⁻¹} := e
    rw [e']
    refine measure_mono fun ω hω hc => hω ?_
    simp only [hCndef, conc1Event, mem_setOf_eq] at hc
    have := (abs_le.1 hc).2
    simp only [hX, hEdef] at hE this ⊢
    nlinarith
  have hB3 : P B3 ≤ f δ := h4 cL hcLr (hcLi.trans (by norm_num))
  have hq : (⟨1 / 2, s⟩ : ℂ) ∈ vSeg s t := mem_vSeg.2 ⟨rfl, le_rfl, hst⟩
  have hqb : (⟨1 / 2, s⟩ : ℂ) ∈ Metric.ball c₅₄ (1 / 20) := by
    rw [Metric.mem_ball, Complex.dist_of_re_eq (by simp [c₅₄]), Real.dist_eq]
    simp only [c₅₄]; rw [abs_lt]; constructor <;> linarith
  have hub : u₅₄ ∈ Metric.ball c₅₄ (1 / 20) := by
    rw [Metric.mem_ball, Complex.dist_of_im_eq (by simp [c₅₄, u₅₄]), Real.dist_eq]
    simp only [c₅₄, u₅₄]; norm_num
  have hvb : v₅₄ ∈ Metric.ball c₅₄ (1 / 20) := by
    rw [Metric.mem_ball, Complex.dist_of_im_eq (by simp [c₅₄, v₅₄]), Real.dist_eq]
    simp only [c₅₄, v₅₄]; norm_num
  have hB5 : P B5 = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (ae_lgd_K₅₄_lt_top (P := P) hW hγ hγ2
      hδ0 hub hqb))
    simp only [mem_setOf_eq] at hω ⊢
    intro hlt; apply hω
    exact lt_of_le_of_lt (iInf₂_le_of_le u₅₄ (mem_singleton _) (iInf₂_le _ hq)) hlt
  have hB6 : P B6 = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (ae_lgd_K₅₄_lt_top (P := P) hW hγ hγ2
      hδ0 hvb hqb))
    simp only [mem_setOf_eq] at hω ⊢
    intro hlt; apply hω
    exact lt_of_le_of_lt (iInf₂_le_of_le v₅₄ (mem_singleton _) (iInf₂_le _ hq)) hlt
  have k1 := measure_union_le (μ := P) (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5) B6
  have k2 := measure_union_le (μ := P) (B1 ∪ B2 ∪ B3 ∪ B4) B5
  have k3 := measure_union_le (μ := P) (B1 ∪ B2 ∪ B3) B4
  have k4 := measure_union_le (μ := P) (B1 ∪ B2) B3
  have k5 := measure_union_le (μ := P) B1 B2
  rw [hB6, add_zero] at k1
  rw [hB5, add_zero] at k2
  have hU : P (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6) < 1 := by
    refine lt_of_le_of_lt (k1.trans (k2.trans (k3.trans (add_le_add (k4.trans
      (add_le_add k5 le_rfl)) le_rfl)))) (lt_of_le_of_lt ?_ h1)
    rw [two_mul]
    gcongr
    · exact hB2.trans hCn
  have hne : B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 ≠ univ := fun h => by
    rw [h, measure_univ] at hU; exact lt_irrefl _ hU
  obtain ⟨ω, hω⟩ := (ne_univ_iff_exists_notMem _).1 hne
  simp only [mem_union, not_or] at hω
  obtain ⟨⟨⟨⟨⟨hω1, hω2⟩, hω3⟩, hω4⟩, hω5⟩, hω6⟩ := hω
  -- the deterministic contradiction
  have hc : ω ∈ Cn := not_not.1 hω1
  simp only [hCndef, conc1Event, mem_setOf_eq] at hc
  have hXu : logMinLGD (ν ω) δ {u₅₄} (vSeg s t) ≤ (χ - ι / 2) * Real.log δ⁻¹ := by
    have := (abs_le.1 hc).2
    simp only [hX, hEdef] at hE this ⊢
    nlinarith
  have hQu := lgdMinSet_le_of_log_le hδ0 (not_not.1 hω5) hXu
  have hQv := lgdMinSet_le_of_log_le hδ0 (not_not.1 hω6) (not_not.1 hω2)
  obtain ⟨d, hdκ, hd1, N, hN, hpairs⟩ := not_not.1 hω3
  have hd : 0 < d := lt_of_lt_of_le (Real.rpow_pos_of_pos hδ0 κ) hdκ
  have hLin : ∀ x ∈ vSeg s t, |x.re - cL.re| ≤ 2 * d ∧ |x.im - cL.im| ≤ 2 * d := by
    intro x hx
    obtain ⟨e1, e2, e3⟩ := mem_vSeg.1 hx
    refine ⟨by simp only [cL]; rw [e1, sub_self, abs_zero]; positivity, ?_⟩
    simp only [cL]; rw [abs_le]; constructor <;> linarith
  have hg := glue₅₄ (ν := dzzMuIn γ W ω) hd hd1 (c := cL) rfl hcLi hpairs hLin
  have hlow : ENNReal.ofReal (δ ^ (-(χ - ι / 4))) ≤
      ((lgdDZZ (dzzWall K₅₄ (dzzMuIn γ W ω)) δ u₅₄ v₅₄ : ℕ∞) : ℝ≥0∞) := not_not.1 hω4
  have hg' := ENat.toENNReal_le.2 hg
  rw [ENat.toENNReal_add, ENat.toENNReal_add] at hg'
  have hNr : ((((80 * N : ℕ) : ℕ∞)) : ℝ≥0∞) ≤ ENNReal.ofReal (2 * δ ^ (-(χ - ι))) := by
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast at hN ⊢
    linarith
  have hfin : ENNReal.ofReal (δ ^ (-(χ - ι / 4))) ≤
      ENNReal.ofReal (2 * δ ^ (-(χ - ι / 2)) + 2 * δ ^ (-(χ - ι))) := by
    have ha : 0 ≤ δ ^ (-(χ - ι / 2)) := (Real.rpow_pos_of_pos hδ0 _).le
    have hb' : 0 ≤ δ ^ (-(χ - ι)) := (Real.rpow_pos_of_pos hδ0 _).le
    rw [ENNReal.ofReal_add (by positivity) (by positivity), two_mul, ENNReal.ofReal_add ha ha]
    calc _ ≤ _ := hlow
      _ ≤ _ := hg'
      _ ≤ _ := add_le_add (add_le_add hQu hQv) hNr
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  exact cfg_arith hι hδ0 hδ1 h3 hfin

end DZZ
end LQGMetric
