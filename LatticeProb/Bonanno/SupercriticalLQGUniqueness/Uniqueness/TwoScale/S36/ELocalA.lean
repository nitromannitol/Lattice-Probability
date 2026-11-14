/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ELocalA at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import LatticeProb.Bonanno.LQGMetric.Meas.UM
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.SLUMetricAPI2
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112M4
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreB
import LatticeProb.Bonanno.SLUFieldSupport
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.LocalEventToolkit
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicCore
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGP
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import Mathlib.Algebra.Order.Round
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.WeylScale
import LatticeProb.Bonanno.LQGMetric.Metric.CurveLength
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Analysis.Convex.PathConnected
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepCross
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.CanonicalH
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.Smoothing




 














set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC DistOn addConst restrictTo)

 

section ScaleOptimal

variable {d₁ e₁ d₂ e₂ : LSCMetric} {k : ℝ≥0∞}

end ScaleOptimal

 

 
abbrev muH {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) : Measure DistC :=
  (P.prod BiLipschitz.OneScale.standardGaussian).map (BiLipschitz.OneScale.gaussianShift h)

theorem muH_isProb {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsWholePlaneGFF h P) : IsProbabilityMeasure (muH P h) :=
  (Measure.isProbabilityMeasure_map_iff
    (BiLipschitz.OneScale.gff_gaussianShift P h hh).measurable.aemeasurable).2 inferInstance

section Canonical

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistC)

 
end Canonical

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
