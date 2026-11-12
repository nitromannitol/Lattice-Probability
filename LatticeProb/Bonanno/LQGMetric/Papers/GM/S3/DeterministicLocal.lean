/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicPath
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

/-!
# GM Lemma 3.1, the events `E(z)` and their locality (task P2-M2D)

GM, `literature/src/1905.00383/uniqueness-final.tex` l. 1190–1201 (proof of Lemma 3.1). GM's
event (3.1): `∃ u, v ∈ B_R(0)` with `D̃_h(u,v)/D_h(u,v) > C`, `D_h(u,v) ≤ D_h(u, ∂B_R(0))` and
`D̃_h(u,v) ≤ D̃_h(u, ∂B_R(0))`; "by Axiom II (locality) … this event is determined by `h|_{B_R(0)}`".

We take `u, v` in the countable set `Qc` of points with rational coordinates and strict
inequalities (`GM.gmCond`), and we sandwich GM's event between itself and an event
`GM.locCond` phrased with the internal metrics on a larger open set `V ⊇ cl V₀`:

* `GM.locCond_of_gmCond`: GM's condition implies the internal one (by `internal_eq_of_lt_…`,
  GM S3.1, `Metric/InternalC`);
* `GM.ratio_of_locCond`: the internal one implies `C D_h(u,v) < D̃_h(u,v)`
  (`internal_le_edist_of_lt_iInf_frontier`);
* `GM.aeEventIn_locCond`: the internal event is a.s. an event of `σ(h|_V)` (Axiom II, LM Lemma
  1.1 continuity of the internal metric, and a countable dense subset `T` of `∂V₀`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.GM

open MetricGeometry Blueprint

/-- points with rational coordinates -/
def Qc : Set ℂ := range fun q : ℚ × ℚ => ((q.1 : ℝ) : ℂ) + ((q.2 : ℝ) : ℂ) * Complex.I

lemma countable_Qc : Qc.Countable := countable_range _

/-- GM's condition (3.1) at `(u, v)` for `V₀` (strict form) -/
def gmCond (D D' : ContMetric) (C : ℝ) (V₀ : Set ℂ) (u v : ℂ) : Prop :=
  ENNReal.ofReal C * edist (D.pt u) (D.pt v) < edist (D'.pt u) (D'.pt v) ∧
    edist (D.pt u) (D.pt v) < Metric.infEDist (D.pt u) (D.pt '' frontier V₀) ∧
    edist (D'.pt u) (D'.pt v) < Metric.infEDist (D'.pt u) (D'.pt '' frontier V₀)

/-- the internal condition at `(u, v)` for `V₀ ⊆ V` -/
def locCond (D D' : ContMetric) (C : ℝ) (V₀ V : Set ℂ) (u v : ℂ) : Prop :=
  ENNReal.ofReal C * D.internal V u v < D'.internal V u v ∧
    D'.internal V u v < ⨅ x ∈ frontier V₀, D'.internal V u x

theorem locCond_of_gmCond {D D' : ContMetric} (hD : D.IsLength) (hD' : D'.IsLength) {C : ℝ}
    {V₀ V : Set ℂ} (hV₀ : IsOpen V₀) (hcl : closure V₀ ⊆ V) {u v : ℂ} (hu : u ∈ V₀)
    (h : gmCond D D' C V₀ u v) : locCond D D' C V₀ V u v := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsub : D.pt '' V₀ ⊆ D.pt '' V := image_mono (subset_closure.trans hcl)
  have hsub' : D'.pt '' V₀ ⊆ D'.pt '' V := image_mono (subset_closure.trans hcl)
  obtain ⟨-, e1⟩ := ContMetric.internal_eq_of_lt_infEDist_frontier hD hV₀ hu h2
  obtain ⟨-, e2⟩ := ContMetric.internal_eq_of_lt_infEDist_frontier hD' hV₀ hu h3
  have i1 : D.internal V u v ≤ edist (D.pt u) (D.pt v) :=
    (internalEDist_anti hsub _ _).trans e1.le
  have i2 : D'.internal V u v = edist (D'.pt u) (D'.pt v) :=
    le_antisymm ((internalEDist_anti hsub' _ _).trans e2.le) (edist_le_internalEDist _ _ _)
  have i3 : Metric.infEDist (D'.pt u) (D'.pt '' frontier V₀) ≤
      ⨅ x ∈ frontier V₀, D'.internal V u x :=
    le_iInf₂ fun x hx => (Metric.infEDist_le_edist_of_mem
      (show D'.pt x ∈ D'.pt '' frontier V₀ from ⟨x, hx, rfl⟩)).trans
      (edist_le_internalEDist _ _ _)
  refine ⟨?_, ?_⟩
  · rw [i2]; exact (mul_le_mul' le_rfl i1).trans_lt h1
  · rw [i2]; exact h3.trans_le i3

theorem ratio_of_locCond {D D' : ContMetric} (hD' : D'.IsLength) {C : ℝ} {V₀ V : Set ℂ}
    (hV₀ : IsOpen V₀) (hcl : closure V₀ ⊆ V) {u v : ℂ} (hu : u ∈ V₀)
    (h : locCond D D' C V₀ V u v) :
    ENNReal.ofReal C * edist (D.pt u) (D.pt v) < edist (D'.pt u) (D'.pt v) :=
  ((mul_le_mul' le_rfl (edist_le_internalEDist _ _ _)).trans_lt h.1).trans_le
    (internal_le_edist_of_lt_iInf_frontier hD' hV₀ hcl hu h.2)

/-- the internal condition for functions `J, J'` in place of the internal metrics, with the
infimum over a countable `T ⊆ ∂V₀` -/
def locSet (C : ℝ) (V₀ T : Set ℂ) : Set ((ℂ → ℂ → ℝ≥0∞) × (ℂ → ℂ → ℝ≥0∞)) :=
  ⋃ u ∈ Qc ∩ V₀, ⋃ v ∈ Qc ∩ V₀,
    ({p | ENNReal.ofReal C * p.1 u v < p.2 u v} ∩ {p | p.2 u v < ⨅ x ∈ T, p.2 u x})

theorem measurableSet_locSet (C : ℝ) (V₀ : Set ℂ) {T : Set ℂ} (hT : T.Countable) :
    MeasurableSet (locSet C V₀ T) := by
  have hm : ∀ u v : ℂ, Measurable fun p : (ℂ → ℂ → ℝ≥0∞) × (ℂ → ℂ → ℝ≥0∞) => p.1 u v :=
    fun u v => (measurable_pi_apply v).comp ((measurable_pi_apply u).comp measurable_fst)
  have hm' : ∀ u v : ℂ, Measurable fun p : (ℂ → ℂ → ℝ≥0∞) × (ℂ → ℂ → ℝ≥0∞) => p.2 u v :=
    fun u v => (measurable_pi_apply v).comp ((measurable_pi_apply u).comp measurable_snd)
  refine MeasurableSet.biUnion (countable_Qc.mono inter_subset_left) fun u _ =>
    MeasurableSet.biUnion (countable_Qc.mono inter_subset_left) fun v _ => ?_
  exact (measurableSet_lt ((hm u v).const_mul _) (hm' u v)).inter
    (measurableSet_lt (hm' u v) (Measurable.biInf T hT fun x _ => hm' u x))

/-- inf over `∂V₀` = inf over a dense `T`, for `D(u,·;V)` continuous on `V ⊇ ∂V₀` -/
lemma iInf_frontier_eq {D : ContMetric} (hD : D.IsLength) {V₀ : Set ℂ} {V : Opens ℂ}
    (hfr : frontier V₀ ⊆ V) {T : Set ℂ} (hT : T ⊆ frontier V₀) (hTd : frontier V₀ ⊆ closure T)
    {u : ℂ} (hu : u ∈ V) :
    ⨅ x ∈ frontier V₀, D.internal V u x = ⨅ x ∈ T, D.internal V u x := by
  refine le_antisymm (iInf₂_mono' fun x hx => ⟨x, hT hx, le_rfl⟩) (le_iInf₂ fun x hx => ?_)
  have hc : ContinuousOn (fun y => D.internal V u y) V := by
    have := ContMetric.continuousOn_internal D hD V.isOpen
    exact this.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y hy => ⟨hu, hy⟩)
  have hxV : x ∈ (V : Set ℂ) := hfr hx
  have hcw : ContinuousWithinAt (fun y => D.internal V u y) T x :=
    (hc x hxV).mono (hT.trans hfr)
  have hne : (𝓝[T] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hTd hx)
  exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun y hy => iInf₂_le y hy)

/-- **GM l. 1196–1199** ("this event is determined by `h|_{B_R(0)}`"), internal form. -/
theorem aeEventIn_locCond {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → DistC} (hg : IsGFFPlusCont g P) (C : ℝ)
    {V₀ : Set ℂ} {V : Opens ℂ} (hV₀ : V₀ ⊆ V) (hfr : frontier V₀ ⊆ V) {T : Set ℂ}
    (hTc : T.Countable) (hT : T ⊆ frontier V₀) (hTd : frontier V₀ ⊆ closure T) :
    AEEventIn P (fieldSigma g V)
      {ω | ∃ u ∈ Qc ∩ V₀, ∃ v ∈ Qc ∩ V₀, locCond (D (g ω)) (D' (g ω)) C V₀ V u v} := by
  obtain ⟨F, hF, hFae⟩ := hD.locality P g hg V
  obtain ⟨F', hF', hFae'⟩ := hD'.locality P g hg V
  let Φ : DistOn V → (ℂ → ℂ → ℝ≥0∞) × (ℂ → ℂ → ℝ≥0∞) := fun r => (F r, F' r)
  refine ⟨(fun ω => restrictTo V (g ω)) ⁻¹' (Φ ⁻¹' locSet C V₀ T),
    ⟨_, (hF.prodMk hF') (measurableSet_locSet C V₀ hTc), rfl⟩, ?_⟩
  filter_upwards [hFae, hFae', hD'.length P g hg] with ω h1 h2 hl
  refine propext ⟨fun ⟨u, hu, v, hv, hc⟩ => ?_, fun hmem => ?_⟩
  · simp only [locSet, mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq, Φ]
    refine ⟨u, hu, v, hv, ?_, ?_⟩
    · rw [← h1 u (hV₀ hu.2) v (hV₀ hv.2), ← h2 u (hV₀ hu.2) v (hV₀ hv.2)]; exact hc.1
    · rw [← h2 u (hV₀ hu.2) v (hV₀ hv.2)]
      have : ⨅ x ∈ T, F' (restrictTo V (g ω)) u x = ⨅ x ∈ T, (D' (g ω)).internal V u x :=
        iInf_congr fun x => iInf_congr fun hx => (h2 u (hV₀ hu.2) x (hfr (hT hx))).symm
      rw [this, ← iInf_frontier_eq hl hfr hT hTd (hV₀ hu.2)]
      exact hc.2
  · simp only [locSet, mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq, Φ] at hmem
    obtain ⟨u, hu, v, hv, hc1, hc2⟩ := hmem
    refine ⟨u, hu, v, hv, ?_, ?_⟩
    · rw [h1 u (hV₀ hu.2) v (hV₀ hv.2), h2 u (hV₀ hu.2) v (hV₀ hv.2)]; exact hc1
    · rw [h2 u (hV₀ hu.2) v (hV₀ hv.2)]
      have : ⨅ x ∈ T, F' (restrictTo V (g ω)) u x = ⨅ x ∈ T, (D' (g ω)).internal V u x :=
        iInf_congr fun x => iInf_congr fun hx => (h2 u (hV₀ hu.2) x (hfr (hT hx))).symm
      rw [iInf_frontier_eq hl hfr hT hTd (hV₀ hu.2), ← this]
      exact hc2

end LQGMetric.GM
