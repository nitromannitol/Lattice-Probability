/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.RTMeas2CGlue at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.R18T6Defs
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Basic.ENNReal.Basic
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnzipInvariance
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Complex.RealDeriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegSwap
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Instances.Real.Lemmas
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Topology.PartitionOfUnity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Real.Pointwise
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaOffsets
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.GiryMonad
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.ZoomRadialFinal
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Complex.Exponential
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm11
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.ZeroRegularization
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaLogSing
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeShiftHit
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeAddConstLat
import LatticeProb.Bonanno.QuantumZipper.Proofs.Wire5
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceTRL
import Mathlib.Analysis.Complex.Order
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsMontel
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsHurwitz
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Bases
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeRC3All2Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Convex.Topology
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower1
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeLawRef
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.AdmissibleAux
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.ConditionalExpectation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.TwoRadiusTilt
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.DiscreteSubset
import Mathlib.Probability.Kernel.Representation
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Topology.Sequences
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.MarkovHit
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UnitInterval
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Topology.Algebra.Support
import Mathlib.Data.NNRat.Encodable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS2, part 5: local vague limits on open subsets of `ℍ` from countable window certificates

The planar analogue of `E1.exists_isVagueLimitOnR_of_winW` (E1Glue.lean): rational balls
`B(c_n, r_n)` with `B̄(c_n, 2r_n) ⊆ U` exhaust the open set `U`; vague limits on all of them glue
to a vague limit on `U` (disjointified sum, consistency by uniqueness, partition of unity for test
functions), with finiteness of the approximations only required eventually on compacts. On a
window the limit comes from the Riesz–Markov theorem on `ℍ` (`VagueH.exists_isVagueLimitOn_of_family`)
applied to the approximations weighted by a cut-off `wt n` equal to `1` on the window, with the
countable dense family `GoodMeas.denseFam` (`WinCertC`).

Own elementary bookkeeping, copied from E1Glue.lean.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

/-- The `n`-th rational ball: centre and radius. -/
def winPQC (n : ℕ) : (ℚ × ℚ) × ℚ := (Encodable.decode n).getD ((0, 0), 0)
def cC (n : ℕ) : ℂ := ⟨((winPQC n).1.1 : ℝ), ((winPQC n).1.2 : ℝ)⟩
def rC (n : ℕ) : ℝ := ((winPQC n).2 : ℝ)

/-- The window condition: `B̄(c_n, 2r_n) ⊆ U`. -/
def WinOKC (U : Set ℂ) (n : ℕ) : Prop := 0 < rC n ∧ closedBall (cC n) (2 * rC n) ⊆ U

open Classical in
/-- The `n`-th window of `U`. -/
def winC (U : Set ℂ) (n : ℕ) : Set ℂ := if WinOKC U n then ball (cC n) (rC n) else ∅

theorem isOpen_winC (U : Set ℂ) (n : ℕ) : IsOpen (winC U n) := by
  unfold winC; split_ifs
  · exact isOpen_ball
  · exact isOpen_empty

theorem winC_subset (U : Set ℂ) (n : ℕ) : winC U n ⊆ U := by
  unfold winC; split_ifs with h
  · exact ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith [h.1])).trans h.2)
  · exact empty_subset _

theorem iUnion_winC {U : Set ℂ} (hU : IsOpen U) : ⋃ n, winC U n = U := by
  refine subset_antisymm (iUnion_subset (winC_subset U)) fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 8 by positivity)
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.re - r / 2 < x.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.im - r / 2 < x.im by linarith)
  set c : ℂ := ⟨(a : ℝ), (b : ℝ)⟩ with hc
  have hdist : dist x c < r := by
    rw [Complex.dist_eq]
    calc ‖x - c‖ ≤ |(x - c).re| + |(x - c).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < r / 2 + r / 2 := by
          simp only [Complex.sub_re, Complex.sub_im, hc]
          have h1 : |x.re - a| < r / 2 := by rw [abs_lt]; constructor <;> linarith
          have h2 : |x.im - b| < r / 2 := by rw [abs_lt]; constructor <;> linarith
          linarith
      _ = r := by ring
  have hsub : closedBall c (2 * r) ⊆ U := fun y hy => hball (by
    rw [mem_ball]
    calc dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
      _ < 2 * r + r := by rw [dist_comm c x]; linarith [mem_closedBall.1 hy]
      _ < ε := by linarith)
  refine mem_iUnion.2 ⟨Encodable.encode (((a, b), r) : (ℚ × ℚ) × ℚ), ?_⟩
  have e : winPQC (Encodable.encode (((a, b), r) : (ℚ × ℚ) × ℚ)) = ((a, b), r) := by
    simp [winPQC, Encodable.encodek]
  have hok : WinOKC U (Encodable.encode (((a, b), r) : (ℚ × ℚ) × ℚ)) := by
    unfold WinOKC cC rC; rw [e]; exact ⟨hr0', hsub⟩
  unfold winC
  rw [if_pos hok]
  unfold cC rC; rw [e]
  rw [mem_ball]; exact hdist

theorem exists_closedBall_subset_winC {U : Set ℂ} {n : ℕ} {x : ℂ} (hx : x ∈ winC U n) :
    ∃ ε > 0, closedBall x ε ⊆ winC U n := by
  have hO := isOpen_winC U n
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hO x hx
  exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hb⟩

/-- Disjointified windows. -/
def winDC (U : Set ℂ) (n : ℕ) : Set ℂ := winC U n \ ⋃ m < n, winC U m

theorem measurableSet_winDC (U : Set ℂ) (n : ℕ) : MeasurableSet (winDC U n) :=
  (isOpen_winC U n).measurableSet.diff
    (MeasurableSet.biUnion (to_countable _) fun m _ => (isOpen_winC U m).measurableSet)

theorem pairwise_disjoint_winDC (U : Set ℂ) : Pairwise (Function.onFun Disjoint (winDC U)) := by
  intro n m hnm
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨hxn, hxn'⟩ ⟨hxm, hxm'⟩
  rcases lt_or_gt_of_ne hnm with h | h
  · exact hxm' (mem_biUnion h hxn)
  · exact hxn' (mem_biUnion h hxm)

theorem iUnion_winDC (U : Set ℂ) : ⋃ n, winDC U n = ⋃ n, winC U n := by
  refine subset_antisymm (iUnion_mono fun n => diff_subset) fun x hx => ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx
  classical
  let m := Nat.find (⟨n, hn⟩ : ∃ n, x ∈ winC U n)
  refine mem_iUnion.2 ⟨m, Nat.find_spec (⟨n, hn⟩ : ∃ n, x ∈ winC U n), ?_⟩
  simp only [mem_iUnion, not_exists]
  intro k hk hxk
  exact Nat.find_min (⟨n, hn⟩ : ∃ n, x ∈ winC U n) hk hxk

/-- The glued measure. -/
def glueC (U : Set ℂ) (ν : ℕ → Measure ℂ) : Measure ℂ :=
  Measure.sum fun n => (ν n).restrict (winDC U n)

theorem restrict_glueC {U : Set ℂ} (hU : IsOpen U) {μs : ℕ → Measure ℂ} {ν : ℕ → Measure ℂ}
    (hν : ∀ n, IsVagueLimitOn (winC U n) μs (ν n)) (m : ℕ) :
    (glueC U ν).restrict (winC U m) = ν m := by
  have hcons : ∀ n, (ν n).restrict (winC U n ∩ winC U m) =
      (ν m).restrict (winC U n ∩ winC U m) := fun n =>
    isVagueLimitOn_unique ((isOpen_winC U n).inter (isOpen_winC U m))
      (isVagueLimitOn_restrict_R18 ((isOpen_winC U n).inter (isOpen_winC U m))
        inter_subset_left (hν n))
      (isVagueLimitOn_restrict_R18 ((isOpen_winC U n).inter (isOpen_winC U m))
        inter_subset_right (hν m))
  ext A hA
  have hWm := (isOpen_winC U m).measurableSet
  rw [Measure.restrict_apply hA, glueC, Measure.sum_apply _ (hA.inter hWm)]
  have hterm : ∀ n, (ν n).restrict (winDC U n) (A ∩ winC U m) =
      ν m (A ∩ winC U m ∩ winDC U n) := fun n => by
    rw [Measure.restrict_apply (hA.inter hWm)]
    have hsub : A ∩ winC U m ∩ winDC U n ⊆ winC U n ∩ winC U m := fun x hx =>
      ⟨hx.2.1, hx.1.2⟩
    rw [← Measure.restrict_eq_self (ν n) hsub, hcons n, Measure.restrict_eq_self (ν m) hsub]
  simp_rw [hterm]
  rw [← measure_iUnion (fun i j hij => (pairwise_disjoint_winDC U hij).mono inter_subset_right
    inter_subset_right) (fun n => (hA.inter hWm).inter (measurableSet_winDC U n)),
    ← inter_iUnion, iUnion_winDC, iUnion_winC hU,
    inter_eq_left.2 (inter_subset_right.trans (winC_subset U m))]
  have h0 : ν m (winC U m)ᶜ = 0 := (hν m).1
  have hae : ∀ᵐ x ∂ν m, x ∈ winC U m :=
    (measure_eq_zero_iff_ae_notMem.1 h0).mono fun x hx => by simpa using hx
  rw [← Measure.restrict_apply hA, Measure.restrict_eq_self_of_ae_mem hae]

/-- **Gluing** (eventual finiteness on compacts suffices). -/
theorem exists_isVagueLimitOn_of_winC {U : Set ℂ} (hU : IsOpen U) {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, μs k K < ⊤)
    (hW : ∀ n, ∃ ν, IsVagueLimitOn (winC U n) μs ν) :
    ∃ ν, IsVagueLimitOn U μs ν := by
  classical
  choose ν hν using hW
  set μ := glueC U ν with hμ
  have hres := restrict_glueC hU hν
  have h0 : μ Uᶜ = 0 := by
    rw [hμ, glueC, Measure.sum_apply _ hU.measurableSet.compl]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    convert measure_empty (μ := ν n)
    exact eq_empty_of_forall_notMem fun x hx =>
      hx.1 (winC_subset U n (diff_subset hx.2))
  have hK : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤ := fun K hKc hKU => by
    refine hKc.measure_lt_top_of_nhdsWithin fun x hx => ?_
    rw [← iUnion_winC hU] at hKU
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hKU hx)
    obtain ⟨ε, hε, hsub⟩ := exists_closedBall_subset_winC hn
    refine ⟨ball x ε, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hε), ?_⟩
    calc μ (ball x ε) ≤ μ (closedBall x ε) := measure_mono ball_subset_closedBall
      _ = (μ.restrict (winC U n)) (closedBall x ε) := by
          rw [Measure.restrict_apply measurableSet_closedBall, inter_eq_left.2 hsub]
      _ < ⊤ := by rw [hres]; exact (hν n).2.1 _ (isCompact_closedBall x ε) hsub
  refine ⟨μ, h0, hK, fun f hf hfc hfU => ?_⟩
  set K := tsupport f with hKdef
  have hKc : IsCompact K := hfc
  obtain ⟨s, hs⟩ := hKc.elim_finite_subcover (winC U) (isOpen_winC U)
    (by rw [iUnion_winC hU]; exact hfU)
  set e := s.equivFin
  set S : Fin s.card → Set ℂ := fun i => winC U (e.symm i) with hS
  obtain ⟨g, hgS, hg1, -, hgc⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun i => isOpen_winC U (e.symm i)) hKc (t := K) (s := S) (by
      intro x hx
      obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.1 (hs hx)
      exact mem_iUnion.2 ⟨e ⟨n, hn⟩, by simp only [hS, Equiv.symm_apply_apply]; exact hxn⟩)
  have hsplit : ∀ t, f t = ∑ i, f t * g i t := fun t => by
    rw [← Finset.mul_sum]
    by_cases ht : t ∈ K
    · have := hg1 ht
      simp only [Finset.sum_apply, Pi.one_apply] at this
      rw [this, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hfg : ∀ i, Continuous fun t => f t * g i t := fun i => hf.mul (g i).continuous
  have hfgc : ∀ i, HasCompactSupport fun t => f t * g i t := fun i => hfc.mul_right
  have hfgS : ∀ i, tsupport (fun t => f t * g i t) ⊆ S i := fun i =>
    (tsupport_mul_subset_right).trans (hgS i)
  have hzero : ∀ i t, t ∉ K → f t * g i t = 0 := fun i t ht => by
    rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have hint : ∀ᶠ k in atTop, ∫ t, f t ∂μs k = ∑ i, ∫ t, f t * g i t ∂μs k := by
    filter_upwards [hfin K hKc hfU] with k hk
    have hfinK : IsFiniteMeasure ((μs k).restrict K) := isFiniteMeasure_restrict.2 hk.ne
    have hsK : ∀ φ : ℂ → ℝ, (∀ t, t ∉ K → φ t = 0) →
        ∫ t, φ t ∂μs k = ∫ t, φ t ∂(μs k).restrict K :=
      fun φ hφ => (setIntegral_eq_integral_of_forall_compl_eq_zero hφ).symm
    rw [hsK f fun t ht => image_eq_zero_of_notMem_tsupport ht]
    simp_rw [fun i => hsK _ (hzero i)]
    rw [← integral_finset_sum _ fun i _ => (hfg i).integrable_of_hasCompactSupport (hfgc i)]
    exact integral_congr_ae (ae_of_all _ fun t => hsplit t)
  have hμK : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 (hK K hKc hfU).ne
  have hlim : ∫ t, f t ∂μ = ∑ i, ∫ t, f t * g i t ∂μ := by
    have hsK : ∀ φ : ℂ → ℝ, (∀ t, t ∉ K → φ t = 0) → ∫ t, φ t ∂μ = ∫ t, φ t ∂μ.restrict K :=
      fun φ hφ => (setIntegral_eq_integral_of_forall_compl_eq_zero hφ).symm
    rw [hsK f fun t ht => image_eq_zero_of_notMem_tsupport ht]
    simp_rw [fun i => hsK _ (hzero i)]
    rw [← integral_finset_sum _ fun i _ => (hfg i).integrable_of_hasCompactSupport (hfgc i)]
    exact integral_congr_ae (ae_of_all _ fun t => hsplit t)
  rw [hlim]
  refine (tendsto_congr' hint).2 (tendsto_finset_sum _ fun i _ => ?_)
  have hi := (hν (e.symm i)).2.2 _ (hfg i) (hfgc i) (hfgS i)
  have e1 : ∫ t, f t * g i t ∂μ = ∫ t, f t * g i t ∂ν (e.symm i) := by
    rw [← hres (e.symm i), setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hfgS i h))]
  rw [e1]; exact hi

end RTMeas
end R18
end QuantumZipper
