/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.BLb at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate
import LatticeProb.Bonanno.SLUMetricAPI2
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import LatticeProb.Bonanno.LQGMetric.Topo.Shortcut
import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutRadial
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import Mathlib.Order.Interval.Set.Union
import LatticeProb.Bonanno.LQGMetric.Metric.CurveLength
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.LQGMetric.Metric.WeylConcat
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.GeodSelN
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.WeylScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.SLUMetricAPI
import Mathlib




 














set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem internal_anti (D : LSCMetric) {Y Z : Set ℂ} (hYZ : Y ⊆ Z) {x y : ℂ} (hx : x ∈ Y)
    (hy : y ∈ Y) :
    D.internal Z (⟨x, hYZ hx⟩, ⟨y, hYZ hy⟩) ≤ D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) := by
  rw [LSCMetric.internal_eq_internalEDist, LSCMetric.internal_eq_internalEDist]
  exact LQGMetric.MetricGeometry.internalEDist_anti (image_mono hYZ) _ _

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
