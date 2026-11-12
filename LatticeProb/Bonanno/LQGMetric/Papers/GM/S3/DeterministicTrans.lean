/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicTrans at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicGMMeas
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

/-!
# GM Lemma 3.1: translation invariance and positivity of GM's event (task P2-M2D)

GM, `literature/src/1905.00383/uniqueness-final.tex`:

* `GM.prob_gmEv_translate` (l. 1203: "By Axiom IV′ and the translation invariance of the law of
  `h`, modulo additive constant, the probability of `E(z)` does not depend on `z`");
* `GM.exists_gmEv_pos` (l. 1190–1193: "There is some large deterministic `R > 0` such that with
  positive probability … after possibly increasing `R` …"), from DFGPS Lemma 3.8
  (`Blueprint.DFGPSLem3_8`, `D_h(u, ∂B_r(0)) → ∞`), as GM cites it (U:1197, blueprint row 6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.GM

open Blueprint

lemma Qc_add {u z : ℂ} (hu : u ∈ Qc) (hz : z ∈ Qc) : u + z ∈ Qc := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hu
  obtain ⟨⟨c, d⟩, rfl⟩ := hz
  exact ⟨(a + c, b + d), by push_cast; ring⟩

lemma Qc_neg {z : ℂ} (hz : z ∈ Qc) : -z ∈ Qc := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hz
  exact ⟨(-a, -b), by push_cast; ring⟩

lemma iInf_sphere_translate (f : ℂ → ℝ≥0∞) (z : ℂ) (ρ : ℝ) :
    ⨅ x ∈ Metric.sphere z ρ, f x = ⨅ y ∈ Metric.sphere (0 : ℂ) ρ, f (y + z) := by
  refine le_antisymm (le_iInf₂ fun y hy => iInf₂_le (y + z) ?_) (le_iInf₂ fun x hx => ?_)
  · simp only [Metric.mem_sphere, dist_eq_norm, sub_zero, add_sub_cancel_right] at hy ⊢
    exact hy
  · have hx' : x - z ∈ Metric.sphere (0 : ℂ) ρ := by
      simp only [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx ⊢; exact hx
    have := iInf₂_le (f := fun y (_ : y ∈ Metric.sphere (0 : ℂ) ρ) => f (y + z)) (x - z) hx'
    simpa only [sub_add_cancel] using this

/-- translating GM's event (3.1) by `z ∈ Qc` (pathwise form of Axiom IV′) -/
theorem gmEv_translate_iff {D D' : DistC → ContMetric} {C R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ Qc) {g g' : DistC} (h1 : ∀ u v, (D g').1 (u, v) = (D g).1 (u + z, v + z))
    (h2 : ∀ u v, (D' g').1 (u, v) = (D' g).1 (u + z, v + z)) :
    g ∈ gmEv D D' C R z ↔ g' ∈ gmEv D D' C R 0 := by
  have hρ : R / 2 ≠ 0 := by positivity
  simp only [gmEv, gmCond_iff, frontier_ball _ hρ, mem_ofPred_eq, h1, h2]
  simp only [iInf_sphere_translate _ z]
  have hb : ∀ u : ℂ, u ∈ Metric.ball z (R / 2) ↔ u - z ∈ Metric.ball (0 : ℂ) (R / 2) := by
    intro u; simp only [Metric.mem_ball, dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨u, ⟨huQ, hub⟩, v, ⟨hvQ, hvb⟩, hc⟩
    refine ⟨u - z, ⟨Qc_add huQ (Qc_neg hz), (hb u).1 hub⟩, v - z,
      ⟨Qc_add hvQ (Qc_neg hz), (hb v).1 hvb⟩, ?_⟩
    simpa only [sub_add_cancel] using hc
  · rintro ⟨u, ⟨huQ, hub⟩, v, ⟨hvQ, hvb⟩, hc⟩
    refine ⟨u + z, ⟨Qc_add huQ hz, (hb _).2 (by simpa using hub)⟩, v + z,
      ⟨Qc_add hvQ hz, (hb _).2 (by simpa using hvb)⟩, hc⟩

/-- **GM l. 1203**: `P[E(z)]` does not depend on `z` (for `z ∈ Qc`). -/
theorem prob_gmEv_translate {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (C : ℝ) {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ Qc) :
    P (h ⁻¹' gmEv D D' C R z) = P (h ⁻¹' gmEv D D' C R 0) := by
  rw [← prob_gmEv_eq hD hD' (hh.affineComp one_pos z) hh C R 0]
  refine measure_congr ?_
  filter_upwards [hD.translation P h (detGFFPlusCont hh) z,
    hD'.translation P h (detGFFPlusCont hh) z] with ω h1 h2
  exact propext (gmEv_translate_iff hR hz h1 h2)

/-- the ratio condition is invariant under a common factor `e > 0` -/
lemma ratio_iff_of_scale {D₁ D₁' D₂ D₂' : ContMetric} {C e : ℝ} (he : 0 < e)
    (h1 : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (h2 : ∀ u v, D₂'.1 (u, v) = e * D₁'.1 (u, v))
    (u v : ℂ) :
    ENNReal.ofReal C * edist (D₂.pt u) (D₂.pt v) < edist (D₂'.pt u) (D₂'.pt v) ↔
      ENNReal.ofReal C * edist (D₁.pt u) (D₁.pt v) < edist (D₁'.pt u) (D₁'.pt v) := by
  have hκ0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  simp only [ContMetric.edist_pt, h1, h2, ENNReal.ofReal_mul he.le]
  rw [mul_left_comm, ENNReal.mul_lt_mul_iff_right hκ0 ENNReal.ofReal_ne_top]

/-- `ratioEv` is a.s. unchanged when a random constant is added to the field (Axiom III) -/
theorem ratioEv_ae_eq_addConst {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (C : ℝ) (a : Ω → ℝ) :
    ratioEv D D' C h =ᵐ[P] ratioEv D D' C (fun ω => addConst (h ω) (a ω)) := by
  filter_upwards [hD.ae_dist_addConst (detGFFPlusCont hh),
    hD'.ae_dist_addConst (detGFFPlusCont hh)] with ω h1 h2
  refine propext ⟨fun ⟨u, hu, v, hv, hc⟩ => ⟨u, hu, v, hv, ?_⟩,
    fun ⟨u, hu, v, hv, hc⟩ => ⟨u, hu, v, hv, ?_⟩⟩
  · exact (ratio_iff_of_scale (Real.exp_pos _) (fun u v => h1 (a ω) u v)
      (fun u v => h2 (a ω) u v) u v).2 hc
  · exact (ratio_iff_of_scale (Real.exp_pos _) (fun u v => h1 (a ω) u v)
      (fun u v => h2 (a ω) u v) u v).1 hc

/-- **GM l. 1190–1193** with DFGPS Lemma 3.8: if `P[C_* > C] > 0` (in the form `ratioEv`), then
GM's event (3.1) has positive probability for some radius. -/
theorem exists_gmEv_pos (h38 : DFGPSLem3_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (C : ℝ) (hpos : 0 < P (ratioEv D D' C h)) :
    ∃ R : ℕ, 0 < R ∧ 0 < P (h ⁻¹' gmEv D D' C R 0) := by
  set h₀ : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0) with h₀_def
  have hm : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  have hh₀ : IsWholePlaneGFF h₀ P := hh.addConst hm
  have hn : IsNormalizedWPGFF h₀ P := ⟨hh₀, by
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh 0 one_pos] with ω hω
    simp only [h₀_def, hω, add_neg_cancel]⟩
  have hpos₀ : 0 < P (ratioEv D D' C h₀) := by
    rwa [← measure_congr (ratioEv_ae_eq_addConst hD hD' hh C _)]
  have hsub : ratioEv D D' C h₀ ≤ᵐ[P] ⋃ R : ℕ, h₀ ⁻¹' gmEv D D' C R 0 := by
    filter_upwards [h38 γ hγ hγ2 D c hD P h₀ hn, h38 γ hγ hγ2 D' c' hD' P h₀ hn]
      with ω hK hK' hmem
    obtain ⟨u, hu, v, hv, hc⟩ := hmem
    have T1 := ((hK.1 {u} isCompact_singleton).comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (two_pos : (0 : ℝ) < 2))).eventually
      (eventually_gt_nhds (edist_lt_top ((D (h₀ ω)).pt u) ((D (h₀ ω)).pt v)))
    have T2 := ((hK'.1 {u} isCompact_singleton).comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (two_pos : (0 : ℝ) < 2))).eventually
      (eventually_gt_nhds (edist_lt_top ((D' (h₀ ω)).pt u) ((D' (h₀ ω)).pt v)))
    have T3 := (tendsto_natCast_atTop_atTop.atTop_div_const (two_pos : (0 : ℝ) < 2)).eventually
      (eventually_gt_atTop (max ‖u‖ ‖v‖))
    obtain ⟨R, hR1, hR2, hR3, hR4⟩ :=
      ((eventually_ge_atTop 1).and (T1.and (T2.and T3))).exists
    have hρ : ((R : ℝ) / 2) ≠ 0 := by
      have : (1 : ℝ) ≤ R := by exact_mod_cast hR1
      positivity
    have hsd : ∀ (E : ContMetric), setDist E {u} (Metric.sphere 0 ((R : ℝ) / 2)) ≤
        Metric.infEDist (E.pt u) (E.pt '' frontier (Metric.ball 0 ((R : ℝ) / 2))) := by
      intro E
      rw [frontier_ball _ hρ]
      exact MetricGeometry.setEDist_le_infEDist ⟨u, rfl, rfl⟩
    simp only [Function.comp_apply] at hR2 hR3 hR4
    refine mem_iUnion.2 ⟨R, u, ⟨hu, ?_⟩, v, ⟨hv, ?_⟩, hc, hR2.trans_le (hsd _),
      hR3.trans_le (hsd _)⟩
    · rw [mem_ball_zero_iff]; exact (le_max_left _ _).trans_lt hR4
    · rw [mem_ball_zero_iff]; exact (le_max_right _ _).trans_lt hR4
  have hex : ∃ R : ℕ, 0 < P (h₀ ⁻¹' gmEv D D' C R 0) := by
    by_contra hne
    push Not at hne
    have h0 : P (⋃ R : ℕ, h₀ ⁻¹' gmEv D D' C R 0) = 0 :=
      measure_iUnion_null fun R => le_antisymm (hne R) zero_le
    exact (measure_mono_ae hsub).trans_eq h0 |>.not_gt hpos₀
  obtain ⟨R, hR⟩ := hex
  refine ⟨R, Nat.pos_of_ne_zero fun h0 => ?_, ?_⟩
  · subst h0
    have : gmEv D D' C ((0 : ℕ) : ℝ) 0 = ∅ := by
      ext g; simp [gmEv]
    rw [this, preimage_empty, measure_empty] at hR
    exact lt_irrefl _ hR
  · rwa [prob_gmEv_eq hD hD' hh hh₀]

end LQGMetric.GM
