/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicGMMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicGM
import LatticeProb.Bonanno.LQGMetric.Meas.CR
import LatticeProb.Bonanno.LQGMetric.Meas.Geod
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicLaw

/-!
# GM Lemma 3.1: measurability and constant invariance of GM's event (3.1) (task P2-M2D)

* `GM.measurableSet_gmEv`: `gmEv D D' C R z` is a Borel set of fields (countable reduction CR1,
  `Meas/CR`, for the boundary distance);
* `GM.gmEv_iff_of_scale`: `gmEv` is invariant when both `D_g`, `D̃_g` are multiplied by the same
  `e > 0` (so, by Axiom III, under `g ↦ g + a`; GM l. 1200).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.GM

open Blueprint

lemma infEDist_pt_image (D : ContMetric) (u : ℂ) (S : Set ℂ) :
    Metric.infEDist (D.pt u) (D.pt '' S) = ⨅ x ∈ S, ENNReal.ofReal (D.1 (u, x)) := by
  rw [Metric.infEDist, iInf_image]
  exact iInf_congr fun x => iInf_congr fun _ => ContMetric.edist_pt D u x

/-- `gmCond` with real distances -/
lemma gmCond_iff (D D' : ContMetric) (C : ℝ) (V₀ : Set ℂ) (u v : ℂ) :
    gmCond D D' C V₀ u v ↔
      ENNReal.ofReal C * ENNReal.ofReal (D.1 (u, v)) < ENNReal.ofReal (D'.1 (u, v)) ∧
      ENNReal.ofReal (D.1 (u, v)) < ⨅ x ∈ frontier V₀, ENNReal.ofReal (D.1 (u, x)) ∧
      ENNReal.ofReal (D'.1 (u, v)) < ⨅ x ∈ frontier V₀, ENNReal.ofReal (D'.1 (u, x)) := by
  rw [gmCond, infEDist_pt_image, infEDist_pt_image, ContMetric.edist_pt, ContMetric.edist_pt]

lemma measurable_contMetric_apply {D : DistC → ContMetric} (hDm : Measurable D) (p : ℂ × ℂ) :
    Measurable fun g => (D g).1 p :=
  (continuous_contMetric_apply.comp (continuous_id.prodMk continuous_const)).measurable.comp hDm

theorem measurableSet_gmEv {D D' : DistC → ContMetric} (hDm : Measurable D)
    (hD'm : Measurable D') (C R : ℝ) (z : ℂ) : MeasurableSet (gmEv D D' C R z) := by
  have hm : ∀ (D : DistC → ContMetric), Measurable D → ∀ u v : ℂ,
      Measurable fun g => ENNReal.ofReal ((D g).1 (u, v)) :=
    fun D hD u v => ENNReal.measurable_ofReal.comp (measurable_contMetric_apply hD (u, v))
  have hinf : ∀ (D : DistC → ContMetric), Measurable D → ∀ (u : ℂ) (S : Set ℂ),
      Measurable fun g => ⨅ x ∈ S, ENNReal.ofReal ((D g).1 (u, x)) := fun D hD u S =>
    measurable_biInf_of_continuous (f := fun g x => ENNReal.ofReal ((D g).1 (u, x)))
      (fun g => ENNReal.continuous_ofReal.comp
        ((D g).1.continuous.comp (continuous_const.prodMk continuous_id)))
      (fun x => hm D hD u x) S
  have e : gmEv D D' C R z = ⋃ u ∈ Qc ∩ Metric.ball z (R / 2), ⋃ v ∈ Qc ∩ Metric.ball z (R / 2),
      ({g | ENNReal.ofReal C * ENNReal.ofReal ((D g).1 (u, v)) < ENNReal.ofReal ((D' g).1 (u, v))}
        ∩ {g | ENNReal.ofReal ((D g).1 (u, v)) <
            ⨅ x ∈ frontier (Metric.ball z (R / 2)), ENNReal.ofReal ((D g).1 (u, x))}
        ∩ {g | ENNReal.ofReal ((D' g).1 (u, v)) <
            ⨅ x ∈ frontier (Metric.ball z (R / 2)), ENNReal.ofReal ((D' g).1 (u, x))}) := by
    ext g
    simp only [gmEv, gmCond_iff, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop, and_assoc]
  rw [e]
  refine MeasurableSet.biUnion (countable_Qc.mono inter_subset_left) fun u _ =>
    MeasurableSet.biUnion (countable_Qc.mono inter_subset_left) fun v _ => ?_
  exact ((measurableSet_lt ((hm D hDm u v).const_mul _) (hm D' hD'm u v)).inter
    (measurableSet_lt (hm D hDm u v) (hinf D hDm u _))).inter
    (measurableSet_lt (hm D' hD'm u v) (hinf D' hD'm u _))

/-- invariance of `gmEv` under a common factor `e > 0` of both metrics -/
theorem gmEv_iff_of_scale {D D' : DistC → ContMetric} {C R : ℝ} {z : ℂ} {g₁ g₂ : DistC} {e : ℝ}
    (he : 0 < e) (h1 : ∀ u v, (D g₂).1 (u, v) = e * (D g₁).1 (u, v))
    (h2 : ∀ u v, (D' g₂).1 (u, v) = e * (D' g₁).1 (u, v)) :
    g₂ ∈ gmEv D D' C R z ↔ g₁ ∈ gmEv D D' C R z := by
  have hκ0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  have hκ : ENNReal.ofReal e ≠ ⊤ := ENNReal.ofReal_ne_top
  have k1 : ∀ u v, ENNReal.ofReal ((D g₂).1 (u, v)) = ENNReal.ofReal e * ENNReal.ofReal ((D g₁).1 (u, v)) :=
    fun u v => by rw [h1, ENNReal.ofReal_mul he.le]
  have k2 : ∀ u v, ENNReal.ofReal ((D' g₂).1 (u, v)) =
      ENNReal.ofReal e * ENNReal.ofReal ((D' g₁).1 (u, v)) :=
    fun u v => by rw [h2, ENNReal.ofReal_mul he.le]
  have kinf : ∀ (f : ℂ → ℝ≥0∞) (S : Set ℂ), ⨅ x ∈ S, ENNReal.ofReal e * f x =
      ENNReal.ofReal e * ⨅ x ∈ S, f x := fun f S => by
    rw [ENNReal.mul_iInf_of_ne hκ0 hκ]
    exact iInf_congr fun x => (ENNReal.mul_iInf_of_ne hκ0 hκ).symm
  simp only [gmEv, gmCond_iff, mem_ofPred_eq, k1, k2, kinf]
  simp only [mul_left_comm (ENNReal.ofReal C), ENNReal.mul_lt_mul_iff_right hκ0 hκ]

/-- a.s. along a whole-plane GFF, `gmEv` is invariant under adding constants (Axiom III) -/
theorem ae_gmEv_addConst_iff {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (C R : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, addConst (h ω) a ∈ gmEv D D' C R z ↔ h ω ∈ gmEv D D' C R z := by
  filter_upwards [hD.ae_dist_addConst (detGFFPlusCont hh),
    hD'.ae_dist_addConst (detGFFPlusCont hh)] with ω h1 h2 a
  exact gmEv_iff_of_scale (Real.exp_pos _) (h1 a) (h2 a)

/-- **GM l. 1203** (law of `h` modulo additive constant): `P[h ∈ gmEv]` is the same for all
whole-plane GFFs, on any probability spaces. -/
theorem prob_gmEv_eq {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω Ω' : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {h : Ω → DistC} {h' : Ω' → DistC}
    (hh : IsWholePlaneGFF h P) (hh' : IsWholePlaneGFF h' P') (C R : ℝ) (z : ℂ) :
    P (h ⁻¹' gmEv D D' C R z) = P' (h' ⁻¹' gmEv D D' C R z) :=
  prob_eq_of_ae_addConst_iff hh hh' (measurableSet_gmEv hD.measurable hD'.measurable C R z)
    (ae_gmEv_addConst_iff hD hD' hh C R z) (ae_gmEv_addConst_iff hD hD' hh' C R z)

end LQGMetric.GM
