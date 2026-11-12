/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_20BilipMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20Bilip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.20: `Lem2_20Bilip` from Lemma 2.13 and translation invariance

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.20, T:1323–1330.
See `L2_20Bilip.lean` for the plan. `lem2_20Bilip : Lem2_13 → Lem2_20Transl → Lem2_20Bilip`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint GM.Tight GM.Bilip

namespace L220

lemma prob_ge_of_compl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s t : Set Ω} (hs : MeasurableSet s) (hst : sᶜ ⊆ t) {a : ℝ} (ha : 0 ≤ a)
    (hlt : P s ≤ ENNReal.ofReal a) : ENNReal.ofReal (1 - a) ≤ P t := by
  rw [ENNReal.ofReal_sub 1 ha, ENNReal.ofReal_one]
  calc 1 - ENNReal.ofReal a ≤ 1 - P s := tsub_le_tsub_left hlt _
    _ = P sᶜ := (prob_compl_eq_one_sub hs).symm
    _ ≤ P t := measure_mono hst

lemma lt_of_lt_sInf {d : C(ℂ × ℂ, ℝ)} {K : Set (ℂ × ℂ)} (hK : IsCompact K) {a : ℝ}
    (ha : a < sInf ((fun p => d p) '' K)) {p : ℂ × ℂ} (hp : p ∈ K) : a < d p :=
  ha.trans_le (csInf_le (hK.image_of_continuousOn d.continuous.continuousOn).bddBelow ⟨p, hp, rfl⟩)

lemma lt_of_sSup_lt {d : C(ℂ × ℂ, ℝ)} {K : Set (ℂ × ℂ)} (hK : IsCompact K) {a : ℝ}
    (ha : sSup ((fun p => d p) '' K) < a) {p : ℂ × ℂ} (hp : p ∈ K) : d p < a :=
  (le_csSup (hK.image_of_continuousOn d.continuous.continuousOn).bddAbove ⟨p, hp, rfl⟩).trans_lt ha

lemma mem_sphere_div {r : ℝ} (hr : 0 < r) {z x : ℂ} {ρ : ℝ} (hx : x ∈ Metric.sphere z (r * ρ)) :
    (x - z) / r ∈ Metric.sphere (0 : ℂ) ρ ∧ (r : ℂ) * ((x - z) / r) + z = x := by
  rw [← scaleSet_sphere hr] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have : ((r : ℂ) * u + z - z) / r = u := by rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hr']
  rw [this]
  exact ⟨hu, rfl⟩

end L220

open L220 in
/-- **The bounds T:1325–1330 of the proof of DFGPS Lemma 2.20** from Lemma 2.13 and the
translation invariance `Lem2_20Transl`. -/
theorem lem2_20Bilip (h13 : Lem2_13) (hT : Lem2_20Transl) : Lem2_20Bilip := by
  intro γ hγ hγ2 Ω _ P _ h Dh εn hh hDm hεp hεt hconv q hq
  set ξ := xiGamma γ
  obtain ⟨c, Λ, -, hc, -, H⟩ := h13 γ hγ hγ2 εn hεp hεt
  have H2 := H P h Dh hh hDm hconv
  simp only at H2
  have hpair : Measurable fun ω => (h ω, Dh ω) := hh.1.measurable.prodMk hDm
  set X0 : ℝ → Ω → C(ℂ × ℂ, ℝ) := fun r ω => resc ξ c r 0 (h ω, Dh ω) with hX0def
  have hX0 : ∀ r, (fun ω => ((c r)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) r 0)) •
      (Dh ω).1.comp (scaleArgs r)) = X0 r := fun r => by
    funext ω; ext p; simp [X0, resc, scaleArgs, ξ]
  simp only [hX0] at H2
  obtain ⟨htight, hcl⟩ := H2
  have hXm : ∀ r ∈ Ioi (0 : ℝ), AEMeasurable (X0 r) P := fun r _ =>
    ((measurable_resc ξ c r 0).comp hpair).aemeasurable
  have hq3 : (0 : ℝ≥0∞) < ENNReal.ofReal (q / 3) := ENNReal.ofReal_pos.2 (by positivity)
  -- (A) the crossing lower bound
  have hS12 : (Metric.sphere (0 : ℂ) (1 / 2)).Nonempty := NormedSpace.sphere_nonempty.2 (by norm_num)
  have hS1 : (Metric.sphere (0 : ℂ) 1).Nonempty := NormedSpace.sphere_nonempty.2 (by norm_num)
  have hdS : Disjoint (Metric.sphere (0 : ℂ) (1 / 2)) (Metric.sphere 0 1) :=
    Set.disjoint_left.2 fun x h1 h2 => by
      rw [mem_sphere_zero_iff_norm] at h1 h2; rw [h1] at h2; norm_num at h2
  obtain ⟨a₁, ha₁, HA⟩ := exists_inf_lower_of_metricFamily X0 (Ioi 0) hXm htight hcl
    (isCompact_sphere _ _) (isCompact_sphere _ _) hS12 hS1 hdS hq3
  -- (B) the chain conditions in the annulus `A_{1/2,2}(0)`
  set U : Set ℂ := (annulus 0 (1 / 2) 2 : Set ℂ) with hUdef
  have hUo : IsOpen U := (annulus 0 (1 / 2) 2).isOpen
  have h1U : (1 : ℂ) ∈ U := sphere_subset_annulus_zero (by norm_num) (by norm_num)
    (by simp : (1 : ℂ) ∈ Metric.sphere (0 : ℂ) 1)
  have hUc : IsConnected U := ⟨⟨1, h1U⟩, isPreconnected_annulus_zero (by norm_num)⟩
  have hKU : Metric.sphere (0 : ℂ) 1 ⊆ U := sphere_subset_annulus_zero (by norm_num) (by norm_num)
  obtain ⟨L, hLc, hKL, hLU, hchain⟩ := exists_chain_compact hUo hUc (isCompact_sphere 0 1) hKU
  have hFc : IsCompact (frontier U) := (isBounded_annulus_zero _ _).isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  have hdisj : Disjoint L (frontier U) :=
    (Set.disjoint_iff_inter_eq_empty.2 hUo.inter_frontier_eq).mono_left hLU
  have h0U : (0 : ℂ) ∉ U := fun h0 => by
    have := h0.1; norm_num at this
  have hFne : (frontier U).Nonempty :=
    nonempty_frontier_iff.2 ⟨⟨1, h1U⟩, fun he => h0U (he ▸ mem_univ _)⟩
  obtain ⟨s, hs, HB1⟩ := exists_inf_lower_of_metricFamily X0 (Ioi 0) hXm htight hcl hLc hFc
    (hS1.mono hKL) hFne hdisj hq3
  obtain ⟨b, hb, HB2⟩ := exists_modulus_of_metricFamily X0 (Ioi 0) hXm htight hcl hLc hs hq3
  obtain ⟨N, hN⟩ := hchain b hb
  refine ⟨(N * s + s) / a₁, by positivity, fun z r hr => ?_⟩
  have hcr : 0 < c r := (hc r hr).1
  have hlaw := map_resc_eq hT hγ hγ2 hh hDm hεp hεt hconv c z hr
  have hXz : Measurable fun ω => resc ξ c r z (h ω, Dh ω) := (measurable_resc ξ c r z).comp hpair
  have htransfer : ∀ G : Set C(ℂ × ℂ, ℝ), MeasurableSet G →
      P ((fun ω => resc ξ c r z (h ω, Dh ω)) ⁻¹' G) = P (X0 r ⁻¹' G) := fun G hG => by
    have hm0 : Measurable fun ω => resc (xiGamma γ) c r 0 (h ω, Dh ω) :=
      (measurable_resc _ c r 0).comp hpair
    rw [← Measure.map_apply hXz hG, hlaw, Measure.map_apply hm0 hG]
  set S : DistC → ℝ := fun g => (N * s + s) * c r * Real.exp (ξ * circleAvg g r z) with hSdef
  refine ⟨S, measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (measurable_circleAvg_left r z))), ?_, ?_⟩
  · -- display 1
    set GA : Set C(ℂ × ℂ, ℝ) :=
      {d | sInf ((fun p => d p) '' (Metric.sphere 0 (1 / 2) ×ˢ Metric.sphere 0 1)) ≤ a₁}
    have hGA : IsClosed GA := isClosed_le (continuous_infOn ((isCompact_sphere _ _).prod
      (isCompact_sphere _ _))) continuous_const
    have hPA : P ((fun ω => resc ξ c r z (h ω, Dh ω)) ⁻¹' GA) ≤ ENNReal.ofReal (q / 3) := by
      rw [htransfer GA hGA.measurableSet]; exact (HA r hr).le
    refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (prob_ge_of_compl
      (hXz hGA.measurableSet) ?_ (by positivity) hPA)
    intro ω hω
    have hω' : a₁ < sInf ((fun p => resc ξ c r z (h ω, Dh ω) p) ''
        (Metric.sphere 0 (1 / 2) ×ˢ Metric.sphere 0 1)) := not_le.1 hω
    show ENNReal.ofReal (((N * s + s) / a₁)⁻¹ * S (h ω)) ≤
      setDist (Dh ω) (Metric.sphere z (r / 2)) (Metric.sphere z r)
    have he : ((N * s + s) / a₁)⁻¹ * S (h ω) =
        a₁ * c r * Real.exp (ξ * circleAvg (h ω) r z) := by
      simp only [hSdef]; field_simp
    rw [he, GM.setDist_eq_iInf]
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ENNReal.ofReal_le_ofReal ?_
    rw [show r / 2 = r * (1 / 2) by ring] at hx
    rw [show r = r * 1 by ring] at hy
    obtain ⟨hu, hux⟩ := mem_sphere_div hr hx
    obtain ⟨hv, hvy⟩ := mem_sphere_div hr hy
    have := lt_of_lt_sInf ((isCompact_sphere _ _).prod (isCompact_sphere _ _)) hω'
      (p := ((x - z) / r, (y - z) / r)) ⟨hu, hv⟩
    rw [resc_apply, lt_scaled_iff hcr] at this
    simp only at this
    rw [hux, hvy] at this
    exact this.le
  · -- display 2
    set K2 : Set (ℂ × ℂ) := {p : ℂ × ℂ | p ∈ L ×ˢ L ∧ ‖p.1 - p.2‖ ≤ b}
    have hK2 : IsCompact K2 := (hLc.prod hLc).inter_right
      (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const)
    set GB : Set C(ℂ × ℂ, ℝ) := {d | sInf ((fun p => d p) '' (L ×ˢ frontier U)) ≤ s} ∪
      {d | s ≤ sSup ((fun p => d p) '' K2)}
    have hGB : IsClosed GB := (isClosed_le (continuous_infOn (hLc.prod hFc)) continuous_const).union
      (isClosed_le continuous_const (continuous_supOn hK2))
    refine ⟨resc ξ c r z ⁻¹' GBᶜ, measurable_resc ξ c r z hGB.isOpen_compl.measurableSet,
      fun x hx hlen => ?_, ?_⟩
    · simp only [mem_preimage, GB, mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_le] at hx
      obtain ⟨hx1, hx2⟩ := hx
      set a := s * c r * Real.exp (ξ * circleAvg x.1 r z)
      have ha : 0 < a := by positivity
      have hA : ∀ u ∈ L, ∀ w ∈ frontier U,
          a < x.2.1 (affHomeo r hr.ne' z u, affHomeo r hr.ne' z w) := fun u hu w hw => by
        have := lt_of_lt_sInf (hLc.prod hFc) hx1 (p := (u, w)) ⟨hu, hw⟩
        rw [resc_apply, lt_scaled_iff hcr] at this
        simpa [affHomeo_apply] using this
      have hB : ∀ u ∈ L, ∀ v ∈ L, ‖u - v‖ ≤ b →
          x.2.1 (affHomeo r hr.ne' z u, affHomeo r hr.ne' z v) < a := fun u hu v hv huv => by
        have := lt_of_sSup_lt hK2 hx2 (p := (u, v)) ⟨⟨hu, hv⟩, huv⟩
        rw [resc_apply, scaled_lt_iff hcr] at this
        simpa [affHomeo_apply] using this
      have hann : (annulus z (r / 2) (2 * r) : Set ℂ) = affHomeo r hr.ne' z '' U := by
        rw [show r / 2 = r * (1 / 2) by ring, show 2 * r = r * 2 by ring, ← scaleSet_annulus hr]
        rfl
      refine iSup₂_le fun u' hu' => iSup₂_le fun v' hv' => ?_
      rw [show r = r * 1 by ring] at hu' hv'
      obtain ⟨hu, hux⟩ := mem_sphere_div hr hu'
      obtain ⟨hv, hvx⟩ := mem_sphere_div hr hv'
      have key := internal_le_of_chain hlen hUo hLU (affHomeo r hr.ne' z) ha hA hB
        (hN _ hu _ hv)
      rw [← hann, affHomeo_apply, affHomeo_apply, hux, hvx] at key
      refine key.trans (ENNReal.ofReal_le_ofReal ?_)
      simp only [hSdef, a]
      nlinarith [Real.exp_pos (ξ * circleAvg x.1 r z), hcr]
    · have hPB : P ((fun ω => resc ξ c r z (h ω, Dh ω)) ⁻¹' GB) ≤ ENNReal.ofReal (2 * q / 3) := by
        rw [htransfer GB hGB.measurableSet, preimage_union]
        refine (measure_union_le _ _).trans ?_
        rw [show 2 * q / 3 = q / 3 + q / 3 by ring, ENNReal.ofReal_add (by positivity) (by positivity)]
        exact add_le_add (HB1 r hr).le (HB2 r hr).le
      refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (prob_ge_of_compl
        (hXz hGB.measurableSet) (fun ω hω => ?_) (by positivity) hPB)
      exact hω

end LQGMetric.DFGPS
