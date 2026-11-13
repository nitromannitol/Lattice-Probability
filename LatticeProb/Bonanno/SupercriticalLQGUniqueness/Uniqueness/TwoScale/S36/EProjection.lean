/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.RationalAround
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.SLUMetricAPI2
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField
import LatticeProb.Bonanno.LQGMetric.Meas.UM
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural




 















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

 
theorem measurable_aroundDist_fixed (A : EuclideanAnnulus) :
    Measurable fun D : LSCMetric => aroundDist D A := by
  have h1 : Measurable fun D : LSCMetric =>
      ((D, (A.center, A.innerRadius, A.outerRadius)) : LSCMetric × (ℂ × ℝ × ℝ)) :=
    measurable_id.prodMk measurable_const
  have h2 := TwoScale.Consolidated.measurable_aroundRat.comp h1
  have heq : (fun D : LSCMetric => aroundDist D A) =
      TwoScale.Consolidated.aroundRat ∘ fun D : LSCMetric =>
        ((D, (A.center, A.innerRadius, A.outerRadius)) : LSCMetric × (ℂ × ℝ × ℝ)) := by
    funext D
    exact TwoScale.Consolidated.aroundDist_eq_aroundRat D A
  rw [heq]
  exact h2

 
end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
