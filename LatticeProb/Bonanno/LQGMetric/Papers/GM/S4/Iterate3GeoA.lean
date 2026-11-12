/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.Iterate3GeoA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate3Geo
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Iterate2L420

/-!
# GM Lemma 4.19: the geodesic part of `F_k` — deterministic properties and locality (D81a, G1)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.22 ((4.39), l. 2527–2540)
and Lemma 4.19 (l. 2322–2327, proof l. 2584–2601). Decision `decisions/DEC-81.md`, packet G1.

* `gm_geoSet_sphere` (G1.1, LM Lemma 1.1): the bound of `gmGeoSet` on the dense sequence passes
  to the whole circle `∂B_ρ(z)` (continuity of `D(𝕫, ·; ℂ ∖ cl B_e(z))`, `continuousOn_internal`);
* `gm_geoSet_avoidGeod` (G1.2, GM l. 2597–2601 via `gm_L4_19_of_439`): on `gmGeoSet`,
  `B_ρ(z) ⊆ 𝓑^•_{τc}` and finite-length avoid-geodesics stay in `𝓑^•_{τc}`;
* `gm_geoSet_of_internal_eq` (G1.3, GM "by locality", l. 2587): `gmGeoSet` is saturated for
  agreement of internal metrics on an open `U ⊇ 𝓑^•_{τc'}` (a near-minimal path of length
  `< τc` stays in `𝓑_{τc}(𝕫) ⊆ U`);
* `gm_gmGeo_aeEventIn` (G1.4): `gmGeo k` is a.s. an event of GM's `𝓕_{k+1}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Metric
open scoped ENNReal
open LQGMetric.Blueprint LQGMetric.LocalEvent

namespace LQGMetric.GM

section Det

/-- `gmSph z ρ` is dense in the circle `∂B_ρ(z)` -/
theorem gm_sphere_subset_closure_gmSph (z : ℂ) (ρ : ℝ) :
    sphere z ρ ⊆ closure (range (gmSph z ρ)) := by
  set g : ℝ → ℂ := fun t => z + ρ * Complex.exp ((t : ℂ) * Complex.I) with hg
  have hgc : Continuous g := by
    simp only [hg]; fun_prop
  have h1 : range (gmSph z ρ) = g '' range (TopologicalSpace.denseSeq ℝ) := by
    rw [← range_comp]; rfl
  intro u hu
  have hn : ‖u - z‖ = ρ := by rw [← dist_eq_norm]; exact mem_sphere.1 hu
  have hu' : u = g (Complex.arg (u - z)) := by
    simp only [hg]
    rw [← hn, Complex.norm_mul_exp_arg_mul_I]
    ring
  rw [h1, hu']
  refine image_closure_subset_closure_image hgc ⟨_, ?_, rfl⟩
  rw [(TopologicalSpace.denseRange_denseSeq ℝ).closure_range]; trivial

/-- the internal metric is `∞` from a point outside the domain -/
theorem gm_internal_top_of_notMem (d : ContMetric) {V : Set ℂ} {x : ℂ} (hx : x ∉ V) (y : ℂ) :
    d.internal V x y = ⊤ := by
  unfold ContMetric.internal MetricGeometry.internalEDist
  have : IsEmpty {γ : Path (d.pt x) (d.pt y) // ∀ t, γ t ∈ d.pt '' V} :=
    ⟨fun γ => hx (d.mem_image_pt.1 (by simpa only [Path.source] using γ.2 0))⟩
  exact iInf_of_empty _

/-- on `gmGeoSet`, `𝕫` lies outside the hole `cl B_e(z)` -/
theorem gm_geoSet_far {d : ContMetric} {𝕫 : ℂ} {R c : ℝ} {z : ℂ} {ρ e : ℝ}
    (hG : d ∈ gmGeoSet 𝕫 R c z ρ e) : 𝕫 ∈ (closedBall z e)ᶜ := by
  obtain ⟨θ, -, hn⟩ := hG
  by_contra h𝕫
  have := hn 0
  rw [gm_internal_top_of_notMem d h𝕫, top_le_iff] at this
  exact ENNReal.ofReal_ne_top this

/-- **G1.1** (LM Lemma 1.1): on `lenSet`, the bound of `gmGeoSet` on the dense sequence holds on
the whole circle `∂B_ρ(z)` -/
theorem gm_geoSet_sphere {d : ContMetric} (hd : d ∈ lenSet) {𝕫 : ℂ} {R c : ℝ} {z : ℂ}
    {ρ e : ℝ} (he : 0 < e) (hρe : e < ρ) (hG : d ∈ gmGeoSet 𝕫 R c z ρ e) :
    ∃ θ : ℚ, (θ : ℝ) < tauD d 𝕫 R * c ∧
      ∀ u ∈ sphere z ρ, d.internal (closedBall z e)ᶜ 𝕫 u ≤ ENNReal.ofReal θ := by
  have h𝕫 := gm_geoSet_far hG
  obtain ⟨θ, hθ, hn⟩ := hG
  refine ⟨θ, hθ, fun u hu => ?_⟩
  have hV : IsOpen (closedBall z e)ᶜ := isClosed_closedBall.isOpen_compl
  have hsph : sphere z ρ ⊆ (closedBall z e)ᶜ := fun w hw => by
    rw [mem_compl_iff, mem_closedBall, mem_sphere.1 hw, not_le]; exact hρe
  have hcl : closure (range (gmSph z ρ)) ⊆ (closedBall z e)ᶜ :=
    (closure_minimal (range_subset_iff.2 (gm_gmSph_mem_sphere z (he.le.trans hρe.le)))
      isClosed_sphere).trans hsph
  have hcont : ContinuousOn (fun w => d.internal (closedBall z e)ᶜ 𝕫 w) (closedBall z e)ᶜ :=
    (d.continuousOn_internal (isLength_of_mem_lenSet hd) hV).comp
      (continuousOn_const.prodMk continuousOn_id) fun w hw => ⟨h𝕫, hw⟩
  exact le_on_closure (f := fun w => d.internal (closedBall z e)ᶜ 𝕫 w)
    (g := fun _ => ENNReal.ofReal θ) (by rintro _ ⟨n, rfl⟩; exact hn n) (hcont.mono hcl)
    continuousOn_const (gm_sphere_subset_closure_gmSph z ρ hu)

/-- the last time after `t₁` at which a curve that is outside `B_ρ(z)` at time `t₁` and inside
at time `T` hits `∂B_ρ(z)` (variant of `gm_exists_last_hit`) -/
theorem gm_exists_last_hit' {Q : ℝ → ℂ} {T ρ t₁ : ℝ} {z : ℂ} (ht₁ : t₁ ∈ Icc 0 T)
    (hQc : ContinuousOn Q (Icc 0 T)) (h1 : ρ ≤ ‖Q t₁ - z‖) (hT' : ‖Q T - z‖ < ρ) :
    ∃ τ ∈ Icc 0 T, t₁ ≤ τ ∧ Q τ ∈ sphere z ρ ∧ ∀ s ∈ Ioc τ T, Q s ∈ ball z ρ := by
  set A := {s ∈ Icc 0 T | ρ ≤ ‖Q s - z‖}
  have hAc : IsClosed A := hQc.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hAne : A.Nonempty := ⟨t₁, ht₁, h1⟩
  have hAbd : BddAbove A := ⟨T, fun s hs => hs.1.2⟩
  set τ := sSup A
  have hτA : τ ∈ A := hAc.csSup_mem hAne hAbd
  have hafter : ∀ s ∈ Ioc τ T, Q s ∈ ball z ρ := by
    intro s hs
    rw [mem_ball, dist_eq_norm]
    by_contra hle
    exact absurd (le_csSup hAbd ⟨⟨hτA.1.1.trans hs.1.le, hs.2⟩, not_lt.1 hle⟩) (not_le.2 hs.1)
  have hτT : τ < T := lt_of_le_of_ne hτA.1.2 (fun h => by
    have := hτA.2; rw [h] at this; linarith)
  refine ⟨τ, hτA.1, le_csSup hAbd ⟨ht₁, h1⟩, ?_, hafter⟩
  rw [mem_sphere, dist_eq_norm]
  refine le_antisymm ?_ hτA.2
  have hcw : ContinuousWithinAt (fun s => ‖Q s - z‖) (Ioc τ T) τ :=
    ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt.comp_continuousWithinAt
      ((hQc τ hτA.1).mono fun s hs => ⟨hτA.1.1.trans hs.1.le, hs.2⟩))
  have hmem : τ ∈ closure (Ioc τ T) := by rw [closure_Ioc hτT.ne]; exact ⟨le_rfl, hτT.le⟩
  have := hcw.mem_closure_image hmem
  refine closure_minimal (s := (fun s => ‖Q s - z‖) '' Ioc τ T) (t := Iic ρ) ?_ isClosed_Iic this
  rintro _ ⟨s, hs, rfl⟩
  have := hafter s hs
  rw [mem_ball, dist_eq_norm] at this
  exact this.le

/-- on `gmGeoSet`, the circle `∂B_ρ(z)` lies in `𝓑_{τc}(𝕫)` -/
theorem gm_geoSet_sphere_ballM {d : ContMetric} (hd : d ∈ lenSet) {𝕫 : ℂ} {R c : ℝ} {z : ℂ}
    {ρ e : ℝ} (he : 0 < e) (hρe : e < ρ) (hR : 0 < R) (hc : 0 < c)
    (hG : d ∈ gmGeoSet 𝕫 R c z ρ e) : sphere z ρ ⊆ ballM d 𝕫 (tauD d 𝕫 R * c) := by
  obtain ⟨θ, hθ, hsph⟩ := gm_geoSet_sphere hd he hρe hG
  have hpos : 0 < tauD d 𝕫 R * c := mul_pos (gm_tauD_pos d 𝕫 hR) hc
  intro u hu
  show d.1 (𝕫, u) < tauD d 𝕫 R * c
  have h1 := ((gm_D_le_internal d _ 𝕫 u).trans (hsph u hu)).trans
    (ENNReal.ofReal_le_ofReal (le_max_left (θ : ℝ) 0))
  rw [ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)] at h1
  exact h1.trans_lt (max_lt hθ hpos)

/-- **G1.2** (GM l. 2597–2601, as `gm_L4_19_of_439`, here without `ρ < |𝕫 - z|`): on `gmGeoSet`,
`B_ρ(z) ⊆ 𝓑^•_{τc}` and every finite-length `D(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫`
(`0 < r ≤ e`) stays in `𝓑^•_{τc}` -/
theorem gm_geoSet_avoidGeod {d : ContMetric} (hd : d ∈ lenSet) {𝕫 : ℂ} {R c : ℝ} {z : ℂ}
    {ρ e : ℝ} (he : 0 < e) (hρe : e < ρ) (hR : 0 < R) (hc : 0 < c)
    (hG : d ∈ gmGeoSet 𝕫 R c z ρ e) :
    ball z ρ ⊆ filledBall d 𝕫 (tauD d 𝕫 R * c) ∧
      ∀ (r : ℝ) (x : ℂ) (Q : ℝ → ℂ) (T : ℝ), 0 < r → r ≤ e → IsAvoidGeod d 𝕫 z r x Q T →
        d.len Q 0 T ≠ ⊤ → ∀ s ∈ Icc 0 T, Q s ∈ filledBall d 𝕫 (tauD d 𝕫 R * c) := by
  have hsphB := gm_geoSet_sphere_ballM hd he hρe hR hc hG
  obtain ⟨θ, hθ, hsph⟩ := gm_geoSet_sphere hd he hρe hG
  have hpos : 0 < tauD d 𝕫 R * c := mul_pos (gm_tauD_pos d 𝕫 hR) hc
  have hball := gm_ball_subset_filledBall_of_sphere d hsphB
  refine ⟨hball, fun r x Q T hr hre hQ hfin s hs => ?_⟩
  obtain ⟨hT0, hQc, hQ0, hQT, hxs, hQout, hmin⟩ := id hQ
  have hTin : ‖Q T - z‖ < ρ := by
    rw [hQT, ← dist_eq_norm, mem_sphere.1 hxs]; linarith
  by_cases hex : ∃ t₁ ∈ Icc 0 T, ρ ≤ ‖Q t₁ - z‖
  · obtain ⟨t₁, ht₁, h1⟩ := hex
    obtain ⟨τ, hτ, -, hτs, hafter⟩ := gm_exists_last_hit' ht₁ hQc h1 hTin
    have hV : (closedBall z e)ᶜ ⊆ (ball z r)ᶜ :=
      compl_subset_compl.2 (ball_subset_closedBall.trans (closedBall_subset_closedBall hre))
    have hlen : d.len Q 0 τ ≤ ENNReal.ofReal θ :=
      (gm_avoid_len_le_internal hQ hfin hτ hV).trans (hsph _ hτs)
    by_cases hsτ : s ≤ τ
    · refine subset_closure.trans subset_union_left (?_ : Q s ∈ ballM d 𝕫 _)
      show d.1 (𝕫, Q s) < tauD d 𝕫 R * c
      have h1 := ((gm_D_le_len d Q hs.1).trans ((MetricGeometry.curveLength_mono _ le_rfl
        hsτ).trans hlen)).trans (ENNReal.ofReal_le_ofReal (le_max_left (θ : ℝ) 0))
      rw [hQ0, ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)] at h1
      exact h1.trans_lt (max_lt hθ hpos)
    · exact hball (hafter s ⟨not_le.1 hsτ, hs.2⟩)
  · push Not at hex
    refine hball ?_
    rw [mem_ball, dist_eq_norm]; exact hex s hs

/-- a curve realizing the internal distance up to any excess -/
theorem gm_exists_curve_of_internal_lt (d : ContMetric) {V : Set ℂ} {x y : ℂ} {b : ℝ≥0∞}
    (h : d.internal V x y < b) : ∃ Q : ℝ → ℂ, Continuous Q ∧ Q 0 = x ∧ Q 1 = y ∧
      MapsTo Q (Icc 0 1) V ∧ d.len Q 0 1 < b := by
  unfold ContMetric.internal MetricGeometry.internalEDist at h
  obtain ⟨⟨γ, hγ⟩, hlt⟩ := iInf_lt_iff.1 h
  refine ⟨fun t => d.unpt (γ.extend t), d.continuous_unpt.comp γ.continuous_extend, ?_, ?_,
    fun t ht => ?_, hlt⟩
  · simp only [Path.extend_zero]; rfl
  · simp only [Path.extend_one]; rfl
  · have := hγ ⟨t, ht⟩
    show d.unpt (γ.extend t) ∈ V
    rw [Path.extend_apply γ ht]
    exact d.mem_image_pt (z := d.unpt _) |>.1 this

/-- **G1.3** (GM "by locality", l. 2587): `gmGeoSet` is saturated for the agreement of internal
metrics on an open `U ⊇ 𝓑^•_{τ_R c'}(𝕫; d₁)`, `c ≤ c'` -/
theorem gm_geoSet_of_internal_eq {d₁ d₂ : ContMetric} (h₁ : d₁ ∈ lenSet) (h₂ : d₂ ∈ lenSet)
    {U : Set ℂ} (hU : IsOpen U) (heq : d₁.internal U = d₂.internal U) {𝕫 : ℂ} {R c c' : ℝ}
    {z : ℂ} {ρ e : ℝ} (hc : 0 < c) (hcc' : c ≤ c') (hc' : 1 < c') (hR : 0 < R)
    (hKU : filledBall d₁ 𝕫 (tauD d₁ 𝕫 R * c') ⊆ U) (hG : d₁ ∈ gmGeoSet 𝕫 R c z ρ e) :
    d₂ ∈ gmGeoSet 𝕫 R c z ρ e := by
  have l1 := isLength_of_mem_lenSet h₁
  have l2 := isLength_of_mem_lenSet h₂
  have hτpos := gm_tauD_pos d₁ 𝕫 hR
  obtain ⟨hτ, -⟩ := gm_tk_congr l1 l2 hc' hU heq hτpos hKU
  obtain ⟨θ, hθ, hn⟩ := hG
  refine ⟨θ, by rw [hτ]; exact hθ, fun n => ?_⟩
  set V := (closedBall z e)ᶜ
  set q := gmSph z ρ n
  set s := tauD d₁ 𝕫 R * c
  have hs : 0 < s := mul_pos hτpos hc
  have hsU : ballM d₁ 𝕫 s ⊆ U := subset_closure.trans (subset_union_left.trans
      ((gm_filledBall_mono d₁ 𝕫 (mul_le_mul_of_nonneg_left hcc' hτpos.le)).trans hKU))
  by_contra hlt
  rw [not_le] at hlt
  have hb : d₁.internal V 𝕫 q < min (d₂.internal V 𝕫 q) (ENNReal.ofReal s) :=
    (hn n).trans_lt (lt_min hlt ((ENNReal.ofReal_lt_ofReal_iff hs).2 hθ))
  obtain ⟨Q, hQc, hQ0, hQ1, hQV, hQlen⟩ := gm_exists_curve_of_internal_lt d₁ hb
  have hQU : MapsTo Q (Icc 0 1) U := fun t ht => hsU (by
    show d₁.1 (𝕫, Q t) < s
    have h1 : ENNReal.ofReal (d₁.1 (Q 0, Q t)) < ENNReal.ofReal s :=
      (gm_D_le_len d₁ Q ht.1).trans_lt ((MetricGeometry.curveLength_mono _ le_rfl ht.2).trans_lt
        (hQlen.trans_le (min_le_right _ _)))
    rw [hQ0] at h1
    exact (ENNReal.ofReal_lt_ofReal_iff hs).1 h1)
  have hlen : d₂.len Q 0 1 = d₁.len Q 0 1 :=
    gm_len_eq_of_internal_eq (fun x _ y _ => by rw [heq]) hQc.continuousOn hQU
  have hint : d₂.internal V 𝕫 q ≤ d₂.len Q 0 1 := by
    have := MetricGeometry.internalEDist_le_curveLength (X := d₂.Space) (Y := d₂.pt '' V)
      zero_le_one (d₂.continuous_pt.comp_continuousOn hQc.continuousOn)
      (fun t ht => ⟨Q t, hQV ht, rfl⟩)
    rw [Function.comp_apply, Function.comp_apply, hQ0, hQ1] at this
    exact this
  rw [hlen] at hint
  exact lt_irrefl _ (hint.trans_lt (hQlen.trans_le (min_le_left _ _)))

end Det

section AE
variable {Ω : Type} {m0 m : MeasurableSpace Ω} {P : Measure[m0] Ω}

theorem gm_aeEventIn_union {E₁ E₂ : Set Ω} (h₁ : @AEEventIn Ω m0 P m E₁)
    (h₂ : @AEEventIn Ω m0 P m E₂) : @AEEventIn Ω m0 P m (E₁ ∪ E₂) := by
  obtain ⟨F₁, hF₁, he₁⟩ := h₁
  obtain ⟨F₂, hF₂, he₂⟩ := h₂
  exact ⟨F₁ ∪ F₂, MeasurableSet.union (m := m) hF₁ hF₂, he₁.union he₂⟩

theorem gm_aeEventIn_iInter {ι : Type} [Countable ι] {E : ι → Set Ω}
    (hE : ∀ i, @AEEventIn Ω m0 P m (E i)) : @AEEventIn Ω m0 P m (⋂ i, E i) := by
  choose F hF hEF using hE
  exact ⟨⋂ i, F i, MeasurableSet.iInter (m := m) hF, EventuallyEqSet.countable_iInter hEF⟩

end AE

variable {γ : ℝ} {D : DistC → ContMetric} {c₀ : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- the `gmGeoSet` event is piecewise local for `𝓑^•_{τ_R ck}` (`c ≤ ck`) -/
theorem gm_geo_pieceSig (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {R c ck : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hck : 1 < ck) (hjk : c ≤ ck) (n : ℕ) (S' : Set ℂ) (z : ℂ)
    (ρ e : ℝ) :
    MeasurableSet[gmPieceSig h (fun ω => filledBall (D (h ω)) 𝕫 (tauD (D (h ω)) 𝕫 R * ck)) n S' P]
      {ω | D (h ω) ∈ gmGeoSet 𝕫 R c z ρ e} := by
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  set Bs : Set DistC := D ⁻¹' ({d | dyadicHull n (filledBall d 𝕫 (tauD d 𝕫 R * ck)) = S'} ∩
    gmGeoSet 𝕫 R c z ρ e) with hBs
  have hnull : NullMeasurableSet Bs (P.map h) :=
    gmE_nullMeas_of_an hD.measurable hh.measurable.aemeasurable hlen
      (gmAn_inter (gmE_hullAn 𝕫 R ck n S') (gm_geoSetAn 𝕫 R c z ρ e))
  obtain ⟨F, hF, hEF⟩ := exists_fieldSigma_piece hD P h (Tight.isGFFPlusCont_of_wp hh) hlen
    isOpen_interior hnull (by
      rintro g₁ g₂ h1 h2 heq ⟨hS, hgeo⟩
      have l1 := isLength_of_mem_lenSet h1
      have l2 := isLength_of_mem_lenSet h2
      have hKU : filledBall (D g₁) 𝕫 (tauD (D g₁) 𝕫 R * ck) ⊆ interior S' :=
        hS ▸ subset_interior_dyadicHull n _
      obtain ⟨hτ, hball⟩ := gm_tk_congr l1 l2 hck isOpen_interior heq
        (gm_tauD_pos _ 𝕫 hR) hKU
      refine ⟨?_, gm_geoSet_of_internal_eq h1 h2 isOpen_interior heq hc hjk hck hR hKU hgeo⟩
      show dyadicHull n (filledBall (D g₂) 𝕫 (tauD (D g₂) 𝕫 R * ck)) = S'
      rw [hτ, gm_filledBall_congr (hball _ le_rfl)]; exact hS)
  refine ⟨F, hF, ?_⟩
  filter_upwards [hEF] with ω hω hS
  have := Iff.of_eq hω
  simp only [hBs, mem_preimage, mem_inter_iff, mem_ofPred_eq, hS, true_and] at this
  exact this

/-- the `gmGeoSet` event at threshold `s_{k+1}` is a.s. in `σ(𝓑^•_{t_{k+1}}, h|)` -/
theorem gm_geoEv_aeEventIn_sigA (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (𝕫 : ℂ) {ℓ 𝕣 ε β : ℝ}
    (hℓ𝕣 : 0 < ℓ * 𝕣) (hε : 0 < ε) (k : ℕ) (z : ℂ) (ρ e : ℝ) :
    AEEventIn P (gmSigA D h 𝕫 (s4T D h 𝕫 ℓ 𝕣 ε β (k + 1)))
      {ω | D (h ω) ∈ gmGeoSet 𝕫 (ℓ * 𝕣) (1 + (k + 1) * ε ^ β) z ρ e} := by
  have hβ : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le β
  have hβ2 : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hk0 : 0 ≤ ((k : ℝ) + 1) * ε ^ β := by positivity
  have hck : 1 < 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β) := by push_cast; linarith
  have hjk : 1 + ((k : ℝ) + 1) * ε ^ β ≤ 1 + ((k + 1 : ℕ) : ℝ) * ε ^ β + ε ^ (2 * β) := by
    push_cast; linarith
  have hc0 : 0 < 1 + ((k : ℝ) + 1) * ε ^ β := by linarith
  have hlen := ae_mem_lenSet h38 hγ hγ2 hD P h hh
  simp only [gmSigA, gm_s4T_eq]
  exact aeEventIn_localSigma h (fun ω => gm_filledBall_isClosed _ _ _) fun n =>
    aeEventIn_hullSigma_of_pieces h _ (by
      filter_upwards [hlen] with ω hω; exact gm_filledBall_isBounded_of_lenSet hω 𝕫 _) n
      fun s => gm_geo_pieceSig h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hc0 hck hjk n (hullFin n s) z ρ e

/-- **G1.4: `gmGeo k` is a.s. an event of GM's `𝓕_{k+1}`** (GM l. 2587, "by locality") -/
theorem gm_gmGeo_aeEventIn [P.IsComplete] (h38 : DFGPSLem3_8) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c₀) (hh : IsWholePlaneGFF h P) (R : RegPar) (𝕫 𝕨 : ℂ)
    (η : Ω → C(unitInterval, ℂ)) {𝕣 ε β : ℝ} (hℓ𝕣 : 0 < R.ℓ * 𝕣) (hε : 0 < ε)
    (ha : 0 < R.lam 3 * ε * 𝕣) (k : ℕ) :
    AEEventIn P (gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) (gmGeo D h R 𝕫 𝕣 ε β k) := by
  have hT : setSigma (fun ω => filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) ≤
      gmAESigma (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) P :=
    (gm_setSigma_le_localSigma h _).trans
      (gm_sigA_ae_mono h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε (Nat.le_succ k))
  have hA : AEEventIn P (gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1)))
      (gmGeo D h R 𝕫 𝕣 ε β k) := by
    refine gm_aeEventIn_iInter fun ab => gm_aeEventIn_iInter fun n => gm_aeEventIn_union ?_ ?_
    · have hG0 := hT _ (gm_G0_measurableSet_setSigma D h 𝕫 𝕫 R.ℓ 𝕣 ε β k (R.lam 0) (R.lam 3)
        R.ν (p4Rads R 𝕣 ε) (gmGridPt (R.lam 0 * ε ^ (1 + R.ν) * 𝕣 / 4) ab) (R.rr 𝕣 ε n) 0 ha)
      obtain ⟨F, hF, hEF⟩ := gm_measurableSet_aeSigma hG0
      exact ⟨Fᶜ, MeasurableSet.compl (m := gmSigA D h 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β (k + 1))) hF,
        hEF.compl⟩
    · exact gm_geoEv_aeEventIn_sigA h38 hγ hγ2 hD hh 𝕫 hℓ𝕣 hε k _ _ _
  obtain ⟨F, hF, hEF⟩ := hA
  exact ⟨F, (le_sup_left : _ ≤ gmSigFk D h 𝕫 𝕨 η R.ℓ 𝕣 ε β (k + 1)) _ hF, hEF⟩

end LQGMetric.GM
