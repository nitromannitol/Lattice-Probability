/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1RadialMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMeas
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarPt
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarJoint
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Polar
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Exp
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import LatticeProb.Bonanno.LQGMetric.Metric.WeylBasic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.MetricSpace.Thickening
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaOffsets
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Real.Pointwise
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaLogSing
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegSwap
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnzipInvariance
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Instances.Real.Lemmas
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Topology.PartitionOfUnity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Connected.LocallyPathConnected
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.CircleIntegral
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import Mathlib.Analysis.Complex.Tietze
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13
import Mathlib.Analysis.Complex.PhragmenLindelof
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Floor
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Increments
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Sequences
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.PathLaw
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm11
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.ZeroRegularization
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.PSeries
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Rat.Cast.Order
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.ZoomRadialFinal
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Real.Pi.Bounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.Analysis.Calculus.ContDiff.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.MeasureTheory.Function.UniformIntegrable
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.SetAlgebra
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1: the radial pairing formula, and Lemma 2.1 unconditionally

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:715–717: for a test function `φ`
radial about `z`, a.s. `⟨g, φ⟩ = ∫_0^∞ 2π r φ(z + r) g_r(z) dr` ("using the circle average
process we may therefore write in polar coordinates").

Proof (`lem2_1RadialPairing`): for every `ω`,
`∫_0^∞ 2π r φ(z + r) ⟨g, σ_{z,r} * ψ_n⟩ dr → ⟨g, φ⟩` (`tendsto_polar_circBump`, deterministic);
and `E ∫_0^∞ 2π r |φ(z + r)| |⟨g, σ_{z,r} * ψ_n⟩ − H(r, z)| dr ≤ K t^n (1 − t)⁻¹`
(Tonelli, `lintegral_enorm_circBump_sub_circleAvg_le`), summable in `n`, so a.s. the polar
integrals of the mollified circle averages converge to `∫_0^∞ 2π r φ(z + r) H(r, z) dr`.

Consequences: `lem2_1PolarPoint`, `lem2_1GffApprox`, and `lem2_1_uncond` (DFGPS Lemma 2.1 for
`IsGFFPlusBddCont h P` and bounded `U`, without open hypotheses).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped Real ENNReal

namespace LQGMetric.DFGPS

open CircleAvg LFPP

lemma continuous_pair_circBump (T : DistC) (n : ℕ) (z : ℂ) :
    Continuous fun r : ℝ => T (circBump n z r) := by
  have : (fun r => T (circBump n z r)) = Real.circleAverage (fun x => T (bumpTest n x)) z :=
    funext fun r => (circleAverage_pairing _ n z r).symm
  rw [this]
  exact Real.Continuous.circleAverage (T.continuous.comp (continuous_bumpTest n))

/-- **The radial pairing formula** (DFGPS T:715–717). -/
theorem lem2_1RadialPairing.{u} : Lem2_1RadialPairing.{u} := by
  intro Ω _ P g H hg hH z φ hrad
  have := hg.gaussian.isProbabilityMeasure
  set ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hν
  set w : ℝ → ℝ := fun r => 2 * π * r * φ (z + (r : ℂ)) with hwdef
  have hwc : Continuous w := by
    simp only [hwdef]
    exact (continuous_const.mul continuous_id).mul
      (φ.continuous.comp (continuous_const.add Complex.continuous_ofReal))
  obtain ⟨R, hR0⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall z
  have hwR : ∀ r : ℝ, R < |r| → w r = 0 := by
    intro r hr
    simp only [hwdef]
    have h0 : φ (z + (r : ℂ)) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
      have := hR0 h
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs] at this
      linarith
    rw [h0, mul_zero]
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  set t : ℝ≥0∞ := ENNReal.ofReal (√(2⁻¹ : ℝ))
  have ht1 : t < 1 := by
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hinv : (1 - t)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt ht1).ne'
  set X : ℕ → ℝ → Ω → ℝ := fun n r ω => g ω (circBump n z r)
  set F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p => ‖w p.2 * (X n p.2 p.1 - H p.2 z p.1)‖ₑ
  have hHm := aemeasurable_circleAvgVersion hg.measurable hH z
  have hFm : ∀ n, AEMeasurable (F n) (P.prod ν) := fun n =>
    (((hwc.measurable.comp measurable_snd).aemeasurable.mul
      ((measurable_pair_circBump hg.measurable n z).aemeasurable.sub hHm))).enorm
  set Δ : ℕ → Ω → ℝ≥0∞ := fun n ω => ∫⁻ r, F n (ω, r) ∂ν
  have hΔm : ∀ n, AEMeasurable (Δ n) P := fun n => (hFm n).lintegral_prod_right'
  -- the constant `K`
  set K : ℝ≥0∞ := ∫⁻ r, ‖w r‖ₑ * ENNReal.ofReal (2 / √r) ∂ν
  have hK : K ≠ ⊤ := by
    set C : ℝ≥0∞ := ENNReal.ofReal (4 * π * √R * M)
    have hle : K ≤ ∫⁻ r, (Iic R).indicator (fun _ => C) r ∂ν := by
      refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
      have hr0 : (0 : ℝ) < r := hr
      by_cases hrR : r ≤ R
      · rw [indicator_of_mem (show r ∈ Iic R from hrR), ← ofReal_norm,
          ← ENNReal.ofReal_mul (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsq : 0 < √r := Real.sqrt_pos.2 hr0
        have e : ‖w r‖ * (2 / √r) = 4 * π * √r * ‖φ (z + (r : ℂ))‖ := by
          simp only [hwdef, norm_mul, Real.norm_eq_abs, abs_of_pos hr0,
            abs_of_pos Real.pi_pos, abs_two]
          field_simp
          rw [Real.sq_sqrt hr0.le]
          ring
        rw [e]
        have h1 : √r ≤ √R := Real.sqrt_le_sqrt hrR
        have h2 := hM (z + (r : ℂ))
        have hM0 : 0 ≤ M := (norm_nonneg _).trans h2
        gcongr
      · rw [hwR r (by rw [abs_of_pos hr0]; linarith), enorm_zero, zero_mul]
        exact zero_le
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_indicator_const measurableSet_Iic, hν, Measure.restrict_apply measurableSet_Iic]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (measure_Icc_lt_top
      (a := (0 : ℝ)) (b := R)).ne (measure_mono fun r hr => ⟨le_of_lt hr.2, hr.1⟩))
  -- the `L¹` bound
  have hEΔ : ∀ n, ∫⁻ ω, Δ n ω ∂P ≤ K * (t ^ n * (1 - t)⁻¹) := by
    intro n
    calc ∫⁻ ω, Δ n ω ∂P = ∫⁻ r, ∫⁻ ω, F n (ω, r) ∂P ∂ν :=
          lintegral_lintegral_swap (f := fun ω r => F n (ω, r)) (hFm n)
      _ ≤ ∫⁻ r, ‖w r‖ₑ * ENNReal.ofReal (2 / √r) * (t ^ n * (1 - t)⁻¹) ∂ν := by
          refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
          have hr0 : (0 : ℝ) < r := hr
          simp only [F, enorm_mul]
          rw [lintegral_const_mul' _ _ enorm_ne_top, mul_assoc, ← mul_assoc (ENNReal.ofReal _)]
          gcongr
          calc ∫⁻ ω, ‖X n r ω - H r z ω‖ₑ ∂P
              = ∫⁻ ω, ‖g ω (circBump n z r) - circleAvg (g ω) r z‖ₑ ∂P := by
                refine lintegral_congr_ae ?_
                filter_upwards [hH.ae_eq r hr0 z] with ω hω
                simp only [X, hω]
            _ ≤ _ := lintegral_enorm_circBump_sub_circleAvg_le hg z hr0 n
      _ = K * (t ^ n * (1 - t)⁻¹) :=
          lintegral_mul_const' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top
            (ne_top_of_lt ht1)) hinv)
  have hsum : ∫⁻ ω, ∑' n, Δ n ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum hΔm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEΔ)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top hK (ENNReal.mul_ne_top hinv hinv)
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hΔm) hsum] with ω hω
  have hΔ0 : Tendsto (fun n => Δ n ω) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have hΔf : ∀ n, Δ n ω < ⊤ := fun n => (ENNReal.le_tsum n).trans_lt hω
  have hHc : ContinuousOn (fun r => H r z ω) (Ioi 0) :=
    (hH.cont ω).comp (continuous_id.prodMk continuous_const).continuousOn
      fun r hr => ⟨hr, mem_univ _⟩
  -- the polar integrals converge to the right-hand side
  have hconv : Tendsto (fun n => ∫ r, w r * X n r ω ∂ν) atTop
      (𝓝 (∫ r, w r * H r z ω ∂ν)) := by
    have hI1 : ∀ n, Integrable (fun r => w r * X n r ω) ν := by
      intro n
      have hc : Continuous fun r => w r * X n r ω := hwc.mul (continuous_pair_circBump (g ω) n z)
      refine (hc.continuousOn.integrableOn_compact (isCompact_Icc (a := 0) (b := R))).of_forall_sdiff_eq_zero
        measurableSet_Ioi fun r ⟨hr, hn⟩ => ?_
      have hr0 : (0 : ℝ) < r := hr
      have : R < r := by
        by_contra hle; exact hn ⟨hr0.le, not_lt.1 hle⟩
      simp only [hwR r (by rw [abs_of_pos hr0]; exact this), zero_mul]
    have hI2 : ∀ n, Integrable (fun r => w r * (X n r ω - H r z ω)) ν := by
      intro n
      refine ⟨ContinuousOn.aestronglyMeasurable (hwc.continuousOn.mul
        ((continuous_pair_circBump (g ω) n z).continuousOn.sub hHc)) measurableSet_Ioi, ?_⟩
      exact hΔf n
    have hdiff : ∀ n, (∫ r, w r * X n r ω ∂ν) - ∫ r, w r * H r z ω ∂ν =
        ∫ r, w r * (X n r ω - H r z ω) ∂ν := by
      intro n
      have e : (fun r => w r * H r z ω) =
          fun r => w r * X n r ω - w r * (X n r ω - H r z ω) := funext fun r => by ring
      rw [e, integral_sub (hI1 n) (hI2 n)]
      ring
    refine tendsto_iff_edist_tendsto_0.2 (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hΔ0 (fun n => zero_le) fun n => ?_)
    rw [edist_eq_enorm_sub, hdiff n]
    exact enorm_integral_le_lintegral_enorm _
  exact tendsto_nhds_unique (tendsto_polar_circBump (g ω) φ z hrad) hconv

/-- The polar formula at a fixed `(ε, z)`, unconditionally. -/
theorem lem2_1PolarPoint.{u} : Lem2_1PolarPoint.{u} := lem2_1PolarPoint_of lem2_1RadialPairing

/-- **The GFF case of DFGPS Lemma 2.1** (T:711–734), unconditionally. -/
theorem lem2_1GffApprox.{u} : Lem2_1GffApprox.{u} :=
  lem2_1GffApprox_of_polarDiff (lem2_1PolarDiff_of lem2_1PolarPoint lem2_1HeatJoint)

/-- **DFGPS Lemma 2.1** (`lem-localized-approx`, T:688–699), without open hypotheses. -/
theorem lem2_1_uncond.{u} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) {U : Set ℂ}
    (hU : Bornology.IsBounded U) (ξ : ℝ) :
    ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × ℂ => if hp : 0 < p.1 then locMollify p.1 hp (h ω) p.2 else 0)
        (Ioi 0 ×ˢ univ) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ closure U,
        |heatMollify ε (h ω) z - locMollify ε hε (h ω) z| ≤ δ) ∧
      ∀ c : ℝ, 1 < c → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z w : ℂ,
        lfppLocOn ξ ε hε (h ω) U z w ≤ ENNReal.ofReal c * lfppDOn ξ (heatMollify ε (h ω)) U z w ∧
        lfppDOn ξ (heatMollify ε (h ω)) U z w ≤ ENNReal.ofReal c * lfppLocOn ξ ε hε (h ω) U z w :=
  lem2_1 lem2_1GffApprox hh hU ξ

end LQGMetric.DFGPS
