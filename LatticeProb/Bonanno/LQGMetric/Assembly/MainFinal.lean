/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Assembly.MainFinal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39KC3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53FN3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53N4F2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53N3F3
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.LFPP.EventMeasurable

/-!
# Theorems 1.1 and 1.2 of Gwynne–Miller (arXiv:1905.00383), with no hypotheses

The statements `Theorem11` and `Theorem12` are the frozen statement layer (LQGMetric/Statement,
tag `statement-frozen-2026-10-01`). The proof is the assembly chain MainOpenF → … → MainOpenQ →
`CONF.theorem11_openR_hbadB` (Papers/CONF/S3T39KC3: CONF Theorem 3.9 discharged by
`CONF.confThm3_9RestAll_holds`, CONF Lemma 2.10 at the domains `confU` by
`CONF.ZBM.confLem2_10AtConfU_holds`), with its last input, the subadditivity event of
Ding–Zeitouni–Zhang (arXiv:1807.00422) Lemma 5.3 in the form `DZZ.L53HbadBAll` (decision D131),
proved here from its two parts:
* node 4 (the endpoints `u`, `v` are desirable), `DZZ.l53Node4PartAll_holds` (S5L53N4F2);
* node 3 (the cells of the chain are desirable, the Peierls step), `DZZ.l53_node3_part`
  (S5L53N3F3).
Every departure from the sources is recorded in DEVIATIONS.md and DECISIONS.md; every error found
in the sources is recorded in ERRATA.md.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

/-- DZZ Lemma 5.3, part 1 (the subadditivity event), in the form `DZZ.L53HbadBAll` (D131). -/
theorem l53HbadBAll_proved : DZZ.L53HbadBAll :=
  DZZ.l53HbadBAll_holds DZZ.l53Node4PartAll_holds DZZ.l53_node3_part

/-- **Theorem 1.1** of Gwynne–Miller, *Existence and uniqueness of the Liouville quantum gravity
metric for γ ∈ (0,2)* (arXiv:1905.00383), as stated in LQGMetric/Statement/Thm11.lean. -/
theorem theorem11_proved : Theorem11 :=
  CONF.theorem11_openR_hbadB l53HbadBAll_proved

/-- **Theorem 1.2** of Gwynne–Miller (arXiv:1905.00383), as stated in LQGMetric/Statement. -/
theorem theorem12_proved : Theorem12 :=
  CONF.theorem12_openR_hbadB l53HbadBAll_proved

/-- **The main result** (decision D38: the final result includes the existence of a whole-plane
GFF, statement audit N1): Theorems 1.1 and 1.2 of Gwynne–Miller (arXiv:1905.00383), together with
the existence of a normalized whole-plane GFF, so that the objects they quantify over exist. -/
theorem main_result : Theorem11 ∧ Theorem12 ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
      (_ : MeasureTheory.IsProbabilityMeasure P) (h : Ω → DistC), IsNormalizedWPGFF h P :=
  ⟨theorem11_proved, theorem12_proved, GFFExist.exists_normalizedWPGFF⟩

open MeasureTheory Filter Topology in
/-- **Theorem 1.1, with the measurability of the events stated explicitly.** For `γ ∈ (0,2)` and a
whole-plane GFF plus a bounded continuous function `h`, there is a random continuous function `Y`,
a.s. a metric and a.s. determined by `h`, such that for all `R, δ > 0` and `ε > 0` the event
`{sup_{B̄_R(0)²} |𝔞_ε⁻¹ D^ε_h − Y| ≥ δ}` is measurable up to a `P`-null set, and its probability
tends to `0` as `ε → 0⁺`: convergence in probability in the usual sense. -/
theorem theorem11_proved_measurable (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusBddCont h P) :
    ∃ Y : Ω → C(ℂ × ℂ, ℝ), (∀ᵐ ω ∂P, IsMetricFn (Y ω)) ∧ AEDeterminedBy Y h P ∧
      (∀ R δ ε : ℝ, 0 < ε → NullMeasurableSet {ω | ENNReal.ofReal δ ≤
        ⨆ p ∈ Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R,
          edist (((aEps (xiGamma γ) ε)⁻¹ • lfppDist (xiGamma γ) ε (h ω)) p) (Y ω p)} P) ∧
      TendstoInProbLU P (fun ε ω => (aEps (xiGamma γ) ε)⁻¹ • lfppDist (xiGamma γ) ε (h ω))
        (𝓝[>] 0) (fun ω => Y ω) := by
  obtain ⟨Y, hmet, hdet, hconv⟩ := theorem11_proved γ hγ hγ2 P h hh
  exact ⟨Y, hmet, hdet, fun R δ ε hε => hh.nullMeasurableSet_lfpp_event hε _
    (hdet.aemeasurable hh.1) _ _, hconv⟩

open MeasureTheory Filter Topology in
/-- **Theorem 1.2 (existence), with the measurability of the events stated explicitly.** For
`γ ∈ (0,2)` there is a strong `γ`-LQG metric `D` such that for every whole-plane GFF plus a bounded
continuous function `h`, all `R, δ > 0` and `ε > 0`, the event
`{sup_{B̄_R(0)²} |𝔞_ε⁻¹ D^ε_h − D_h| ≥ δ}` is measurable up to a `P`-null set, and its probability
tends to `0` as `ε → 0⁺`. -/
theorem theorem12_existence_measurable (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ D : DistC → ContMetric, IsStrongLQGMetric γ D ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        (∀ R δ ε : ℝ, 0 < ε → NullMeasurableSet {ω | ENNReal.ofReal δ ≤
          ⨆ p ∈ Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R,
            edist (((aEps (xiGamma γ) ε)⁻¹ • lfppDist (xiGamma γ) ε (h ω)) p)
              ((D (h ω)).1 p)} P) ∧
        TendstoInProbLU P (fun ε ω => (aEps (xiGamma γ) ε)⁻¹ • lfppDist (xiGamma γ) ε (h ω))
          (𝓝[>] 0) (fun ω => (D (h ω)).1) := by
  obtain ⟨D, hD, hconv⟩ := (theorem12_proved γ hγ hγ2).1
  refine ⟨D, hD, fun P _ h hh => ⟨fun R δ ε hε => ?_, hconv P h hh⟩⟩
  exact hh.nullMeasurableSet_lfpp_event hε _
    ((measurable_subtype_coe.comp (hD.measurable.comp hh.1)).aemeasurable) _ _

end LQGMetric
