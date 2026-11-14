/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Finite at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Good
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_4Tail
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate




 















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC)

 

theorem acr_le_curve_of_endpoint_order (D : LSCMetric) {P : ℝ → ℂ} {s t c d : ℝ} {v : ℂ}
    (hP : D.IsCurve P s t) (hcont : ContinuousOn P (Icc s t)) (hcd : c ≤ d)
    (hs : dist (P s) v ≤ c) (ht : d ≤ dist (P t) v) :
    Objects.CorrectedEvent.acr D v c d ≤ D.len P s t := by
  have hrad : ContinuousOn (fun u => dist (P u) v) (Icc s t) :=
    Continuous.comp_continuousOn (g := fun x : ℂ => dist x v) (by fun_prop) hcont
  obtain ⟨s', t', hss', hs't', ht't, hsc, htd, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hP.1 hrad hcd hs ht
  have hP' : D.IsCurve P s' t' := ⟨hs't', hP.2.mono (Icc_subset_Icc hss' ht't)⟩
  have htrace' : P '' Icc s' t' ⊆ Objects.CorrectedEvent.cann v c d := by
    rintro x ⟨u, hu, rfl⟩
    exact hbetween u hu
  have hcost : Objects.CorrectedEvent.acr D v c d ≤ D.len P s' t' :=
    iInf_le_of_le P <| iInf_le_of_le s' <| iInf_le_of_le t' <|
      iInf_le_of_le hP' <| iInf_le_of_le htrace' <|
        iInf_le_of_le (mem_sphere.mpr hsc) <| iInf_le_of_le (mem_sphere.mpr htd) le_rfl
  exact hcost.trans (LQGMetric.MetricGeometry.curveLength_mono _ hss' ht't)

 


end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
