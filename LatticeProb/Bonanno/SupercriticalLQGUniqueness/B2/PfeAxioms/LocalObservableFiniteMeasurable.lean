/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.Metrizable
import LatticeProb.Bonanno.SLUMetricAPI2
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Support.LSCMetricLowerSemicontinuous
import Mathlib.Topology.Semicontinuity.Basic
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.LscTop.Limits
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import LatticeProb.Bonanno.LQGMetric.Topo.Shortcut
import LatticeProb.Bonanno.LQGMetric.Metric.CurveLength
import LatticeProb.Bonanno.LQGMetric.Metric.WeylConcat
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsLFPPExponent
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7G2
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPWeyl
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.EProjection
import Mathlib.Data.List.ChainOfFn
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import LatticeProb.Bonanno.LQGMetric.Topo.CrosscutRadial
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import Mathlib.Order.Interval.Set.Union
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S6.GeodSelN
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
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
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7N1
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.RationalAround
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgPairing
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylField
import LatticeProb.Bonanno.LQGMetric.Meas.UM
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2P3
import LatticeProb.Bonanno.LQGMetric.Field.GermSplitA
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.LocalEventToolkit
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGP
import Mathlib.Algebra.Order.Round
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35
import Mathlib.Analysis.Convex.PathConnected
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.FieldTranslations
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1StepCross
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulus
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bInv
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43Out
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeWeyl.NormalizedLFPP
import LatticeProb.Bonanno.LQGMetric.LFPP.Length
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylUpper
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreB

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem measurable_normalizedLFPPMetric_comp
    {Ω : Type} [MeasurableSpace Ω]
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    {X : Ω → C(ℂ, ℝ)} (hX : ∀ z, Measurable fun ω => X ω z) :
    Measurable fun ω => PfeWeyl.normalizedLFPPMetric ξ a (X ω) := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  letI : BorelSpace LSCFun := ⟨rfl⟩
  apply B2.LscTop.measurable_iff_toLSCFun.mpr
  have h := B2.LscTop.measurable_rescaledLFPPFun_comp ξ a hX
  convert h using 1
  funext ω
  apply Subtype.ext
  funext p
  exact PfeWeyl.normalizedLFPPMetric_toLSCFun ξ a (X ω) p

end SupercriticalLQGUniqueness.B2.PfeAxioms
