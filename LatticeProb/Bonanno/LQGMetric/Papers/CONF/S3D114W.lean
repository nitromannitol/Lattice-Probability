/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D114W at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36H
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114NA
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112G3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B9

/-!
# CONF Lemma 3.6 in the D114 form: wiring (packet C1)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6 (C:1308–1448); decision D114
(`decisions/DEC-114.md` §2, §4 C1).

* `conf36_propB_of_steps_ae`: `conf36_propB_of_steps` (S3L36G, CONF C:1425–1432) for events
  `F n` that are only a.s. measurable (`AEEventIn P m0 (F n)`, D30), by passing to measurable
  versions `F' n` (the one-step bounds transfer by `measure_congr`, the conditional expectation by
  `condExp_congr_ae`).
* `conf36_lem3_6AtAE0_of_D114`: **`CONFLem3_6AtAE0 γ D c p`** (D114 form) from Lemma 3.3 for
  `fatG p` (`L33Gen γ D c p (fatG p)`), `p.Valid`, `p.δ < 1/8`, `IsWeakLQGMetric γ D c` and the
  two restated nodes `Conf36MeasNodeAE`, `Conf36StepNodeAE` (S3D114NA; D120: a.s. stopping time). The chain inputs are
  `l36Step2Input_fatG'` (S3D112G3; `CONFChainFull 4`, `CONFFullConn` proved), property A is
  `conf36_propA` (S3L36E), the rate is `conf36_rate` (S3L36F).
* `confLem3_5At_delta`: CONF Lemma 3.5 with `p.δ < 1/8` (the parameter chain of D114 §2 (a),
  `confLem3_5_of_3_4`), unconditionally.
* `confLem3_6_of_D114`: **`Blueprint.CONFLem3_6`** from Lemma 3.3 for `fatG` and the two nodes,
  at the parameters of `confLem3_5At_delta`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

section PropB

variable {Ω : Type} {m0 : MeasurableSpace Ω} {P : Measure[m0] Ω}

theorem conf36Avoid_congr_ae {F F' : ℕ → Set Ω} (hFF : ∀ᵐ ω ∂P, ∀ n, (ω ∈ F n ↔ ω ∈ F' n))
    (A : Set Ω) (n : ℕ) : conf36Avoid F A n =ᵐ[P] conf36Avoid F' A n := by
  filter_upwards [hFF] with ω hω
  simp only [conf36Avoid, mem_inter_iff, mem_ofPred_eq, hω]

/-- **CONF Lemma 3.6, property B from the one-step bounds** (C:1425–1432), for a.s. events
`F n` -/
theorem conf36_propB_of_steps_ae [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {F : ℕ → Set Ω} (hF : ∀ n, @AEEventIn Ω m0 P m0 (F n)) {N : Ω → ℕ} (hN : Measurable[m] N)
    {𝔭 : ℝ} (h𝔭 : 0 < 𝔭) (h𝔭1 : 𝔭 < 1)
    (hstep : ∀ j : ℕ, ∀ n < j, ∀ A, MeasurableSet[m] A → A ⊆ {ω | N ω = j} →
      ENNReal.ofReal 𝔭 * P (conf36Avoid F A n) ≤ P (conf36Avoid F A n ∩ F (n + 1))) :
    ∀ᵐ ω ∂P, 1 - (1 - 𝔭) ^ N ω ≤
      (P[{ω | ∃ n, 1 ≤ n ∧ n ≤ N ω ∧ ω ∈ F n}.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  choose F' hF'm hF'e using hF
  have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ F n ↔ ω ∈ F' n) := ae_all_iff.2 fun n => (hF'e n).mem_iff
  have hstep' : ∀ j : ℕ, ∀ n < j, ∀ A, MeasurableSet[m] A → A ⊆ {ω | N ω = j} →
      ENNReal.ofReal 𝔭 * P (conf36Avoid F' A n) ≤ P (conf36Avoid F' A n ∩ F' (n + 1)) := by
    intro j n hn A hA hAj
    have e1 := conf36Avoid_congr_ae hall A n
    rw [← measure_congr e1, ← measure_congr (e1.inter (hF'e (n + 1)))]
    exact hstep j n hn A hA hAj
  have hB := conf36_propB_of_steps hm hF'm hN h𝔭 h𝔭1 hstep'
  have hGe : {ω | ∃ n, 1 ≤ n ∧ n ≤ N ω ∧ ω ∈ F n}.indicator (fun _ => (1 : ℝ)) =ᵐ[P]
      {ω | ∃ n, 1 ≤ n ∧ n ≤ N ω ∧ ω ∈ F' n}.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hall] with ω hω
    have e : (ω ∈ {ω | ∃ n, 1 ≤ n ∧ n ≤ N ω ∧ ω ∈ F n}) ↔
        ω ∈ {ω | ∃ n, 1 ≤ n ∧ n ≤ N ω ∧ ω ∈ F' n} :=
      exists_congr fun n => by rw [hω n]
    by_cases h1 : ω ∈ {ω | ∃ n, 1 ≤ n ∧ n ≤ N ω ∧ ω ∈ F n}
    · rw [indicator_of_mem h1, indicator_of_mem (e.1 h1)]
    · rw [indicator_of_notMem h1, indicator_of_notMem (mt e.2 h1)]
  filter_upwards [hB, condExp_congr_ae (m := m) hGe] with ω h1 h2
  rw [h2]
  exact h1

end PropB

/-- **CONF Lemma 3.5 with `δ < 1/8`** (D114 §2 (a): the parameter choice of CONF L3.2, C:1167,
`confCond2_prob`), unconditionally -/
theorem confLem3_5At_delta {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) :
    ∃ p : CONFParams, p.Valid ∧ p.δ < 1 / 8 ∧ CONFLem3_5At γ D c p :=
  confLem3_5_of_3_4 (confLem3_4_of (confLem3_2_of hγ hγ2 hD confHarmBound)
    (confEMeas_of confHarmLocN hD) confLem2_12aP)

end LQGMetric.CONF
