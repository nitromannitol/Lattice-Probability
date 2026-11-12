/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54I4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54I3

/-!
# D117 P-54T (4): `dzzLem54SegQ_of_cfg` (P2-DZZ54C)

See S5L54I3 for the plan. DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2553–2578, 2271, 611–624.
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

/-- **DZZ (eq-point-to-segment), corrected (`DZZLem54SegQ`), at `μIn`**, for `χ > 0`, from DZZ
L5.3 and the walled P3.17 at `𝕍̃_{u₅₄,v₅₄}`, at `𝕍̃_{u₀,v₀}` (ring crossings) and at the leg walls. -/
theorem dzzLem54SegQ_of_cfg {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {χ ξ : ℝ} (hχ : 0 < χ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80)
    (hL53 : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317 : DZZProp317In P (fun ω => dzzWall (tildeBox u₅₄ v₅₄) (dzzMuIn γ W ω))
      (tildeBox u₅₄ v₅₄) ξ)
    (h317R : DZZProp317In P (fun ω => dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω))
      (tildeBox ringU₀ ringV₀) ξ)
    (hLeg : ∀ u ∈ dzzVbar, DZZProp317Leg P (dzzMuIn γ W) ξ u) :
    DZZLem54SegQ P (dzzMuIn γ W) χ := by
  intro u hu
  haveI := hW.isProbabilityMeasure
  refine ⟨min (ξ * χ / 8) (min (χ / 4) (1 / 2)), 2 / χ, by positivity, by positivity,
    by rw [div_mul_cancel₀ _ hχ.ne'], fun ι hι => ?_⟩
  obtain ⟨hι0, hιι₀⟩ := hι
  have hιa : ι ≤ ξ * χ / 8 := hιι₀.le.trans (min_le_left _ _)
  have hιb : ι ≤ χ / 4 := hιι₀.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hιc : ι ≤ 1 / 2 := hιι₀.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  set κ := 2 / χ * ι with hκdef
  have hκχ : κ * χ = 2 * ι := by rw [hκdef]; field_simp
  have hκ0 : 0 < κ := by positivity
  have hκξ : κ ≤ ξ / 4 := by
    rw [hκdef, div_mul_eq_mul_div, div_le_iff₀ hχ]; nlinarith
  have hκ1 : κ < 1 := by
    rw [hκdef, div_mul_eq_mul_div, div_lt_iff₀ hχ]; nlinarith
  -- the configuration at `ι / 2`
  have hcfg := cfg_whp hW hγ hγ2 (ι := ι / 2) (κ := κ) (by positivity) (by linarith) hκ0
    (by rw [hκχ]; linarith) hκ1 (by linarith) hξ hξ1 hL53 h317 h317R (1 / 8) (by norm_num)
  -- the couplings
  have hcpl : ∀ j : Fin 4, DZZSimCoupleU γ ξ (legSq u (1 / 20) j) (aJ j) := fun j =>
    dzzSimCoupleU_of_norm_le hγ hγ2 hξ (by linarith) (isClosed_sqBox _ _)
      (legSq_subset_dzzVXi hu j hξ.le hξ1) (aJ_ne_zero j) (norm_aJ j).le
  choose Cf hCf hCpl using hcpl
  obtain ⟨cL, hcL, hconcL⟩ := hLeg u hu
  set ε := min (1 / 4) (ι / χ) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 4 := min_le_left _ _
  have hεχ : ε * χ ≤ ι := by
    have := min_le_right (1 / 4 : ℝ) (ι / χ)
    calc ε * χ ≤ ι / χ * χ := by gcongr
      _ = ι := by field_simp
  -- the contradiction
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  classical
  set X : ℝ → Set ℂ → Ω → ℝ := fun δ L ω =>
    logMinLGD (dzzWall (legWall u (1 / 20) L) (dzzMuIn γ W ω)) δ {u} L with hXdef
  set Bad : ℝ → Prop := fun δ => δ ^ (ξ - κ) ≤ 1 / 2 ∧ ¬ ∀ L : Set ℂ,
    IsBdrySeg u (1 / 20) (δ ^ (2 / χ * ι)) L →
      (χ - 2 * ι) * Real.log δ⁻¹ ≤ ∫ ω, X δ L ω ∂P with hBad
  have hch : ∀ δ, ∃ L : Set ℂ, Bad δ → IsBdrySeg u (1 / 20) (δ ^ κ) L ∧
      ∫ ω, X δ L ω ∂P < (χ - 2 * ι) * Real.log δ⁻¹ := by
    intro δ
    by_cases h : Bad δ
    · have h' := h.2
      simp only [not_forall, not_le] at h'
      obtain ⟨L, h1, h2⟩ := h'
      exact ⟨L, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose Lf hLf using hch
  set p₀ : ℂ := ⟨u.re + 1 / 20 / 2, u.im⟩
  set Lg : ℝ → Set ℂ := fun δ => if Bad δ then Lf δ else {p₀} with hLgdef
  have hadm : ∀ δ ∈ Ioo (0 : ℝ) 1, Lg δ ⊆ frontier (sqBox u (1 / 20)) ∧
      IsXiAdmissibleSet ξ δ (Lg δ) := by
    intro δ hδ
    by_cases hb : Bad δ
    · obtain ⟨hseg, -⟩ := hLf δ hb
      simp only [hLgdef, if_pos hb]
      have hk := (Real.rpow_pos_of_pos hδ.1 κ).le
      refine ⟨hseg.1, Or.inr ⟨hseg.isConnected hk, ?_⟩⟩
      refine le_trans ?_ (hseg.diam_ge (by norm_num) hk)
      have e : δ ^ ξ = δ ^ (ξ - κ) * δ ^ κ := by
        rw [← Real.rpow_add hδ.1]; congr 1; ring
      rw [e]
      have := Real.rpow_pos_of_pos hδ.1 κ
      nlinarith [hb.1]
    · simp only [hLgdef, if_neg hb]
      exact ⟨singleton_subset_iff.2 (right_pt_mem_frontier u), Or.inl ⟨_, rfl⟩⟩
  obtain ⟨δ₀, hδ₀, hconc⟩ := hconcL Lg hadm (ι / 4) ⟨by positivity, by linarith⟩
  -- eventual facts
  set e := cL * (ι / 4) ^ 2 with he
  have he0 : 0 < e := by positivity
  have hTd : Tendsto (fun δ : ℝ => δ ^ (1 - ε)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun δ : ℝ => δ ^ (1 - ε)) (𝓝 0) (𝓝 0) := by
        simpa [Real.zero_rpow (by linarith : (1 - ε) ≠ 0)] using
          (Real.continuousAt_rpow_const 0 (1 - ε) (Or.inr (by linarith))).tendsto
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact Real.rpow_pos_of_pos hδ _
  have ev1 := hTd.eventually hcfg
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ (κ / 2) ≤ 1 / 2 := by
    filter_upwards [tendsto_rpow_nhdsGT_zero (show 0 < κ / 2 by positivity)
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with δ h
    exact le_of_lt h
  have ev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ (ξ - κ) ≤ 1 / 2 := by
    filter_upwards [tendsto_rpow_nhdsGT_zero (show 0 < ξ - κ by linarith)
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with δ h
    exact le_of_lt h
  have ev4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (δ ^ e) < 1 / 4 :=
    (tendsto_order.1 (tendsto_ofReal_rpow_zero he0)).2 _ (by norm_num)
  have hlogT : Tendsto (fun δ : ℝ => Real.log δ⁻¹) (𝓝[>] 0) atTop := by
    exact (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr
      (fun δ => by simp [Real.log_inv])
  have ev5 : ∀ j : Fin 4, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Cf j * Real.exp (-(ε * Real.log δ⁻¹) ^ 2 / Cf j) < 1 / 4 := by
    intro j
    have h1 : Tendsto (fun x : ℝ => -(ε * x) ^ 2 / Cf j) atTop atBot := by
      have : Tendsto (fun x : ℝ => (ε * x) ^ 2 / Cf j) atTop atTop :=
        ((tendsto_pow_atTop (two_ne_zero)).comp (tendsto_id.const_mul_atTop hε0)).atTop_div_const
          (hCf j)
      exact (tendsto_neg_atTop_atBot.comp this).congr (fun x => by simp only [Function.comp, neg_div])
    have h2 := ((Real.tendsto_exp_atBot.comp h1).const_mul (Cf j)).comp hlogT
    rw [mul_zero] at h2
    exact (tendsto_order.1 h2).2 _ (by norm_num)
  have ev5' := Filter.eventually_all.2 ev5
  have ev0 := eventually_Ioo_nhdsGT hδ₀
  obtain ⟨δ, hnot, hev⟩ := (hcon.and_eventually (((((ev0.and ev1).and ev2).and ev3).and ev4).and
    ev5')).exists
  obtain ⟨⟨⟨⟨⟨hδ, hδcfg⟩, hδ2⟩, hδ3⟩, hδ4⟩, hδ5⟩ := hev
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ < 1 := hδ.2.trans_le (min_le_right _ _)
  have hb : Bad δ := ⟨hδ3, hnot⟩
  obtain ⟨hseg, hE⟩ := hLf δ hb
  set L := Lf δ with hLdef
  have hLg : Lg δ = L := by
    show (if Bad δ then Lf δ else {p₀}) = L
    rw [if_pos hb]
  have hℓ0 : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ0).2 hδ1)
  obtain ⟨j, hwall, hside, s', t', hs', ht', hl1, hl2, himg⟩ :=
    seg_side (Real.rpow_pos_of_pos hδ0 κ) hseg
  -- the coupling
  set b := c₅₄ - aJ j * legC u j
  have hθ : simMap (aJ j) b = thJ u j := (thJ_eq_simMap u j).symm
  have hθK : simMap (aJ j) b '' legSq u (1 / 20) j ⊆ dzzVXi ξ := by
    rw [hθ]; exact (thJ_legSq u j).trans (K₅₄_subset_dzzVXi hξ.le hξ1)
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hP⟩ := hCpl j b hθK
  haveI := hW₁.isProbabilityMeasure
  set lam := ε * Real.log δ⁻¹ with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set δ' := δ ^ (1 - ε) with hδ'def
  have hδ'eq : ‖aJ j‖ * δ * Real.exp lam = δ' := by
    rw [norm_aJ, one_mul, hlam, exp_mul_log_inv hδ0, ← Real.rpow_one_add' hδ0.le (by linarith)]
    rw [hδ'def, sub_eq_add_neg]
  have hδ'0 : 0 < δ' := Real.rpow_pos_of_pos hδ0 _
  have hδδ' : δ ≤ δ' := by
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ' := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (by linarith)
  have hlog' : Real.log δ'⁻¹ = (1 - ε) * Real.log δ⁻¹ := log_inv_rpow hδ0
  -- the configuration segment is admissible at `δ'`
  have hsegC : SegC κ δ' s' t' := by
    refine ⟨hs', ht', ?_, ?_⟩
    · have e1 : δ' ^ (2 * κ) = δ ^ κ * δ ^ (κ * (1 - 2 * ε)) := by
        rw [hδ'def, ← Real.rpow_mul hδ0.le, ← Real.rpow_add hδ0]; congr 1; ring
      have e2 : δ ^ (κ * (1 - 2 * ε)) ≤ δ ^ (κ / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (by nlinarith)
      have := Real.rpow_pos_of_pos hδ0 κ
      rw [e1]; nlinarith
    · exact hl2.trans (Real.rpow_le_rpow hδ0.le hδδ' hκ0.le)
  have hcfgδ := hδcfg s' t' hsegC
  set c := (χ - ι / 2) * Real.log δ'⁻¹ with hc
  -- transfer to the coupling space
  set T : Set ℕ∞ := {n | Real.log (n.toNat : ℝ) < c}
  have tr1 := prob_lgdMinSet_wall_eq hW hW₁ hγ hγ2 (legWall u (1 / 20) L) δ {u} L T
  have tr2 := prob_lgdMinSet_wall_eq hW hW₂ hγ hγ2 K₅₄ δ' {u₅₄} (vSeg s' t') T
  obtain ⟨x₀, hx₀⟩ := hseg.nonempty (Real.rpow_pos_of_pos hδ0 κ).le
  have tr3 := prob_lgdMinSet_wall_eq hW hW₁ hγ hγ2 (legWall u (1 / 20) L) δ {u} L {⊤}
  have hfin0 : P {ω | lgdMinSet (dzzWall (legWall u (1 / 20) L) (dzzMuIn γ W ω)) δ {u} L ∈
      ({⊤} : Set ℕ∞)} = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (ae_legSq_lt_top (P := P) hW hγ hγ2
      hδ0 hu (hside hx₀)))
    simp only [mem_setOf_eq, mem_singleton_iff] at hω ⊢
    intro hlt
    have hlt' : lgdMinSet (dzzWall (legSq u (1 / 20) j) (dzzMuIn γ W ω)) δ {u} L < ⊤ :=
      lt_of_le_of_lt (iInf₂_le_of_le u (mem_singleton _) (iInf₂_le _ hx₀)) hlt
    rw [hwall] at hω
    exact absurd hω hlt'.ne
  -- the bad set of the coupling
  set G := {ω | ¬ ∀ x ∈ legSq u (1 / 20) j, ∀ y ∈ legSq u (1 / 20) j, ∀ δ : ℝ, 0 < δ →
    lgdDZZ (dzzWall (simMap (aJ j) b '' legSq u (1 / 20) j) (dzzMuIn γ W₂ ω))
        (‖aJ j‖ * δ * Real.exp lam) (simMap (aJ j) b x) (simMap (aJ j) b y) ≤
      lgdDZZ (dzzWall (legSq u (1 / 20) j) (dzzMuIn γ W₁ ω)) δ x y ∧
    lgdDZZ (dzzWall (legSq u (1 / 20) j) (dzzMuIn γ W₁ ω)) δ x y ≤
      lgdDZZ (dzzWall (simMap (aJ j) b '' legSq u (1 / 20) j) (dzzMuIn γ W₂ ω))
        (‖aJ j‖ * δ * Real.exp (-lam)) (simMap (aJ j) b x) (simMap (aJ j) b y)} with hG
  have hGP : P' G ≤ ENNReal.ofReal (Cf j * Real.exp (-lam ^ 2 / Cf j)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hP lam hlam0)
  have hsub : {ω | lgdMinSet (dzzWall (legWall u (1 / 20) L) (dzzMuIn γ W₁ ω)) δ {u} L ∈ T} ⊆
      G ∪ {ω | lgdMinSet (dzzWall K₅₄ (dzzMuIn γ W₂ ω)) δ' {u₅₄} (vSeg s' t') ∈ T} ∪
        {ω | lgdMinSet (dzzWall (legWall u (1 / 20) L) (dzzMuIn γ W₁ ω)) δ {u} L ∈
          ({⊤} : Set ℕ∞)} := by
    intro ω hω
    by_contra hno
    simp only [mem_union, not_or, mem_setOf_eq, mem_singleton_iff] at hno hω
    obtain ⟨⟨hg, h2⟩, h3⟩ := hno
    simp only [hG, mem_setOf_eq, not_not] at hg
    set Q₁ := lgdMinSet (dzzWall (legWall u (1 / 20) L) (dzzMuIn γ W₁ ω)) δ {u} L
    set Q₂ := lgdMinSet (dzzWall K₅₄ (dzzMuIn γ W₂ ω)) δ' {u₅₄} (vSeg s' t')
    have hQ : Q₂ ≤ Q₁ := by
      simp only [Q₁, Q₂, lgdMinSet, iInf_singleton]
      refine le_iInf₂ fun x hx => ?_
      have hxK := hside hx
      have hxK' : x ∈ legSq u (1 / 20) j := by
        rw [legSq_eq]
        exact (sqBox_subset_legSq u (by norm_num) j).trans (le_of_eq (legSq_eq u j))
          (sqSide_subset_sqBox u _ j hxK)
      have huK : u ∈ legSq u (1 / 20) j := by
        rw [legSq_eq]
        exact (sqBox_subset_legSq u (by norm_num) j).trans (le_of_eq (legSq_eq u j))
          ⟨by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, abs_zero]; norm_num⟩
      have hc1 := (hg u huK x hxK' δ hδ0).1
      rw [hδ'eq, hθ, thJ_u] at hc1
      have hc2 : lgdDZZ (dzzWall K₅₄ (dzzMuIn γ W₂ ω)) δ' u₅₄ (thJ u j x) ≤
          lgdDZZ (dzzWall (thJ u j '' legSq u (1 / 20) j) (dzzMuIn γ W₂ ω)) δ' u₅₄
            (thJ u j x) :=
        lgdDZZ_mono_measure (dzzWall_anti (thJ_legSq u j) _) _ _ _
      rw [hwall]
      exact (iInf₂_le _ (himg ⟨x, hx, rfl⟩)).trans (hc2.trans hc1)
    apply h2
    have h1Q : 1 ≤ Q₂ := one_le_lgdMinSet _ _ _ _
    have hQ1 : Q₁ < ⊤ := lt_top_iff_ne_top.2 h3
    show Real.log (Q₂.toNat : ℝ) < c
    exact lt_of_le_of_lt (log_toNat_mono_of_one_le hQ hQ1 h1Q) hω
  have hS : P {ω | X δ L ω < c} ≤ ENNReal.ofReal (Cf j * Real.exp (-lam ^ 2 / Cf j)) +
      ENNReal.ofReal (1 / 8) := by
    have e0 : P {ω | X δ L ω < c} = P {ω | lgdMinSet (dzzWall (legWall u (1 / 20) L)
        (dzzMuIn γ W ω)) δ {u} L ∈ T} := rfl
    rw [e0, tr1]
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    rw [← tr3, hfin0, add_zero]
    refine (measure_union_le _ _).trans (add_le_add hGP ?_)
    rw [← tr2]
    exact hcfgδ
  -- concentration in `Ω`
  have hCn := hconc δ ⟨hδ0, hδ.2.trans_le (min_le_left _ _)⟩
  simp only [hLg] at hCn
  have hsum : P {ω | X δ L ω < c} + P (legConc P (dzzMuIn γ W) u δ (ι / 4) L)ᶜ < 1 := by
    have e14 : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    have ha : ENNReal.ofReal (Cf j * Real.exp (-lam ^ 2 / Cf j)) < ENNReal.ofReal (1 / 4) :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (hδ5 j)
    have hb' : ENNReal.ofReal (1 / 8) < ENNReal.ofReal (1 / 4) :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
    have hc' : ENNReal.ofReal (δ ^ e) < ENNReal.ofReal (1 / 4) := by rw [← e14]; exact hδ4
    calc _ ≤ ENNReal.ofReal (Cf j * Real.exp (-lam ^ 2 / Cf j)) + ENNReal.ofReal (1 / 8) +
          ENNReal.ofReal (δ ^ e) := add_le_add hS hCn
      _ < ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) :=
          ENNReal.add_lt_add (ENNReal.add_lt_add ha hb') hc'
      _ = ENNReal.ofReal (3 / 4) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
      _ < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
  have hne : {ω | X δ L ω < c} ∪ (legConc P (dzzMuIn γ W) u δ (ι / 4) L)ᶜ ≠ univ := by
    intro h
    have := (measure_union_le (μ := P) _ _).trans_lt hsum
    rw [h, measure_univ] at this
    exact lt_irrefl _ this
  obtain ⟨ω, hω⟩ := (ne_univ_iff_exists_notMem _).1 hne
  simp only [mem_union, not_or, mem_setOf_eq, not_lt, not_not] at hω
  obtain ⟨hω1, hω2⟩ := hω
  rw [mem_compl_iff, not_not] at hω2
  simp only [legConc, conc1Event, mem_setOf_eq] at hω2
  have h2 := (abs_le.1 hω2).2
  simp only [hXdef] at hω1 hE
  rw [hc, hlog'] at hω1
  have k1 : ε * χ * Real.log δ⁻¹ ≤ ι * Real.log δ⁻¹ := mul_le_mul_of_nonneg_right hεχ hℓ0.le
  have k2 : 0 ≤ ε * ι * Real.log δ⁻¹ := by positivity
  have k3 : 0 < ι * Real.log δ⁻¹ := by positivity
  linarith

end DZZ
end LQGMetric
