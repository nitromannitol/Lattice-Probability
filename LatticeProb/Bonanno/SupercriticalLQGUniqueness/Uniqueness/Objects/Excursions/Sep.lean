/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Sep at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.BLb
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.SLUMetricAPI2
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulus
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35




 














set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

variable {C : Objects.CorrectedEvent.Constants} {D Db : LSCMetric} {f : C(ℂ, ℝ)} {V : TopologicalSpace.Opens ℂ}
  {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ}

 
theorem internal_le_len_of_mem (D : LSCMetric) {Y : Set ℂ} {π : ℝ → ℂ} {a b p q : ℝ}
    (hπ : D.IsCurve π a b) (hY : ∀ t ∈ Icc a b, π t ∈ Y) (hp : p ∈ Icc a b) (hq : q ∈ Icc a b)
    (hpY : π p ∈ Y) (hqY : π q ∈ Y) :
    D.internal Y (⟨π p, hpY⟩, ⟨π q, hqY⟩) ≤ D.len π a b := by
  rcases le_total p q with hpq | hqp
  · have hc : D.IsCurve π p q := ⟨hpq, hπ.2.mono (Icc_subset_Icc hp.1 hq.2)⟩
    have h := BiLipschitz.Barrier.internal_le_len' D hc (fun t ht => hY t ⟨hp.1.trans ht.1, ht.2.trans hq.2⟩)
    exact h.trans (LQGMetric.MetricGeometry.curveLength_mono _ hp.1 hq.2)
  · have hc : D.IsCurve π q p := ⟨hqp, hπ.2.mono (Icc_subset_Icc hq.1 hp.2)⟩
    have h := BiLipschitz.Barrier.internal_le_len' D hc (fun t ht => hY t ⟨hq.1.trans ht.1, ht.2.trans hp.2⟩)
    rw [(LSCMetric.isExtMetric_internal D Y).2.2.1]
    exact h.trans (LQGMetric.MetricGeometry.curveLength_mono _ hq.1 hp.2)

 
end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
