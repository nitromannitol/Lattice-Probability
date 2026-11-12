/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Deterministic01
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicLocal
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG

/-!
# GM Lemma 3.1, core zero-one statement (task P2-M2D)

GM, `literature/src/1905.00383/uniqueness-final.tex` l. 1190–1206, with decision D15:

* `GM.locEv D D' C R z h`: the event "`∃ u, v ∈ Qc ∩ B_{R/2}(z)` with the internal condition
  `locCond` for the internal metrics on `B_R(z)`" (our form of GM's `E(z)`);
* `GM.aeEventIn_locEv_addConst`: `locEv` is a.s. an event of `σ((h + c)|_{B_R(z)})` for every
  random constant `c` (GM l. 1200: "determined by `h|_{B_R(0)}` viewed modulo additive
  constant", Axiom III);
* `GM.locEv_subset_ratioEv`: `locEv ⊆ {∃ u, v ∈ Qc : C D_h(u,v) < D̃_h(u,v)}` a.s.;
* `GM.measure_ratioEv_eq_one`: if the events `locEv (R • 4k)` have probability `≥ p₀ > 0`,
  then a.s. `C D_h(u,v) < D̃_h(u,v)` for some `u, v` (GM L2.7 in place of tail triviality, D15).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.GM

open MetricGeometry Blueprint

lemma detGFFPlusCont {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) : IsGFFPlusCont h P := by
  refine ⟨hh.measurable, fun _ => 0, measurable_const, ?_⟩
  have h0 : ofCont 0 = 0 := by
    ext φ
    simp [ofCont]
  simpa [h0] using hh

/-- `locCond` is invariant under multiplying both internal metrics by the same `κ ∈ (0, ∞)` -/
lemma locCond_iff_of_scale {D₁ D₁' D₂ D₂' : ContMetric} {C : ℝ} {V₀ V : Set ℂ} {κ : ℝ≥0∞}
    (hκ0 : κ ≠ 0) (hκ : κ ≠ ⊤) (e : ∀ x y, D₂.internal V x y = κ * D₁.internal V x y)
    (e' : ∀ x y, D₂'.internal V x y = κ * D₁'.internal V x y) (u v : ℂ) :
    locCond D₂ D₂' C V₀ V u v ↔ locCond D₁ D₁' C V₀ V u v := by
  have hinf : ⨅ x ∈ frontier V₀, D₂'.internal V u x = κ * ⨅ x ∈ frontier V₀, D₁'.internal V u x := by
    rw [ENNReal.mul_iInf_of_ne hκ0 hκ]
    refine iInf_congr fun x => ?_
    rw [ENNReal.mul_iInf_of_ne hκ0 hκ]
    exact iInf_congr fun _ => e' u x
  rw [locCond, locCond, hinf, e u v, e' u v, mul_left_comm, ENNReal.mul_lt_mul_iff_right hκ0 hκ, ENNReal.mul_lt_mul_iff_right hκ0 hκ]

/-- our form of GM's event `E(z)` (GM l. 1202) -/
def locEv (D D' : DistC → ContMetric) (C R : ℝ) (z : ℂ) {Ω : Type} (h : Ω → DistC) : Set Ω :=
  {ω | ∃ u ∈ Qc ∩ Metric.ball z (R / 2), ∃ v ∈ Qc ∩ Metric.ball z (R / 2),
    locCond (D (h ω)) (D' (h ω)) C (Metric.ball z (R / 2)) (ballO z R) u v}

/-- the event `{∃ u, v ∈ Qc : C D_h(u,v) < D̃_h(u,v)}` -/
def ratioEv (D D' : DistC → ContMetric) (C : ℝ) {Ω : Type} (h : Ω → DistC) : Set Ω :=
  {ω | ∃ u ∈ Qc, ∃ v ∈ Qc,
    ENNReal.ofReal C * edist ((D (h ω)).pt u) ((D (h ω)).pt v) <
      edist ((D' (h ω)).pt u) ((D' (h ω)).pt v)}

lemma closure_ball_half_subset {z : ℂ} {R : ℝ} (hR : 0 < R) :
    closure (Metric.ball z (R / 2)) ⊆ (ballO z R : Set ℂ) :=
  Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith))

lemma frontier_ball_half_subset {z : ℂ} {R : ℝ} (hR : 0 < R) :
    frontier (Metric.ball z (R / 2)) ⊆ (ballO z R : Set ℂ) :=
  frontier_subset_closure.trans (closure_ball_half_subset hR)

theorem locEv_subset_ratioEv {γ : ℝ} {D D' : DistC → ContMetric} {c' : ℝ → ℝ}
    (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (C : ℝ) {R : ℝ}
    (hR : 0 < R) (z : ℂ) : locEv D D' C R z h ≤ᵐ[P] ratioEv D D' C h := by
  filter_upwards [hD'.length P h (detGFFPlusCont hh)] with ω hl hmem
  obtain ⟨u, hu, v, hv, hc⟩ := hmem
  exact ⟨u, hu.1, v, hv.1,
    ratio_of_locCond hl Metric.isOpen_ball (closure_ball_half_subset hR) hu.2 hc⟩

/-- **GM l. 1200** ("determined by `h|_{B_R(0)}` viewed modulo additive constant") -/
theorem aeEventIn_locEv_addConst {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (C : ℝ) {R : ℝ} (hR : 0 < R) (z : ℂ) {a : Ω → ℝ} (ha : Measurable a) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (a ω)) (ballO z R)) (locEv D D' C R z h) := by
  set g : Ω → DistC := fun ω => addConst (h ω) (a ω)
  have hg : IsWholePlaneGFF g P := hh.addConst ha
  obtain ⟨T, hTs, hTc, hTd⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (frontier (Metric.ball z (R / 2)))
      ).exists_countable_dense_subset
  obtain ⟨F, hF, hEF⟩ := aeEventIn_locCond hD hD' (detGFFPlusCont hg) C
    (subset_closure.trans (closure_ball_half_subset hR)) (frontier_ball_half_subset hR) hTc hTs hTd
  refine ⟨F, hF, EventuallyEq.trans ?_ hEF⟩
  filter_upwards [hD.ae_internal_addFun_of_eq_const (detGFFPlusCont hh),
    hD'.ae_internal_addFun_of_eq_const (detGFFPlusCont hh)] with ω h1 h2
  have hκ0 : ENNReal.ofReal (Real.exp (xiGamma γ * a ω)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have e1 := h1 (ContinuousMap.const ℂ (a ω)) (ballO z R) (xiGamma γ * a ω) (ballO z R).isOpen
    (fun _ _ => rfl)
  have e2 := h2 (ContinuousMap.const ℂ (a ω)) (ballO z R) (xiGamma γ * a ω) (ballO z R).isOpen
    (fun _ _ => rfl)
  refine propext ⟨fun ⟨u, hu, v, hv, hc⟩ => ⟨u, hu, v, hv, ?_⟩,
    fun ⟨u, hu, v, hv, hc⟩ => ⟨u, hu, v, hv, ?_⟩⟩
  · exact (locCond_iff_of_scale hκ0 ENNReal.ofReal_ne_top e1 e2 u v).2 hc
  · exact (locCond_iff_of_scale hκ0 ENNReal.ofReal_ne_top e1 e2 u v).1 hc

/-- **Core of GM Lemma 3.1** (l. 1202–1206 with D15): if the events `E(4kR)` have probability
`≥ p₀ > 0`, then a.s. `C D_h(u,v) < D̃_h(u,v)` for some `u, v`. -/
theorem measure_ratioEv_eq_one (hL : L2_7) {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (C : ℝ) {R p₀ : ℝ} (hR : 0 < R) (hp₀ : 0 < p₀)
    (hprob : ∀ k : ℕ, ENNReal.ofReal p₀ ≤ P (locEv D D' C R (R • ((4 * k : ℝ) : ℂ)) h)) :
    P (ratioEv D D' C h) = 1 :=
  measure_eq_one_of_L2_7 hL hh hR hp₀
    (fun z _ ha => aeEventIn_locEv_addConst hD hD' hh C hR z ha) hprob
    (fun _ => locEv_subset_ratioEv hD' hh C hR _)

end LQGMetric.GM
