/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.R18T6Defs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WeldingUniqueness
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.CameronMartin
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
import Mathlib.Probability.Distributions.Gaussian.Real
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.NonVacuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Real.Pointwise
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FiniteArea
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaOffsets
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Connected.LocallyPathConnected
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CarLengthArea
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExt
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdryFold
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdrySurj
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Complex.PhragmenLindelof
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeDistortion
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Increments
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Sequences
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeCovering
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.PathLaw
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Semicontinuity.Basic
import LatticeProb.Bonanno.QuantumZipper.Blueprint.ComplexAnalysis
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedLocal
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.ZoomRadialFinal
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Int
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Complex.Exponential
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm11
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.ZeroRegularization
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdry
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscTV
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.StrongLaw
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Polynomial.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaLogSing
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.ContinuousMap.Weierstrass
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Constructions.Cylinders
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G3Core
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.SetAlgebra
import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.Prop16MeasArea
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeShiftHit
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeAddConstLat
import LatticeProb.Bonanno.QuantumZipper.Proofs.Wire5
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceTRL
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G1FMKolm5
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.F2WedgeCoupleFree
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HarmonicPart
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KernelBasic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsMontel
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsHurwitz
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Bases
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeRC3All2Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnifSWGaussRatio
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.Analysis.Convex.Topology
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower1
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedM7D2
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence
import Mathlib.Probability.Moments.Covariance
import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.Prop16DomCoupleKolm
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeLawRef
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.AdmissibleAux
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeKolm
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G3SchemeCI
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.TwoRadiusTilt
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.DiscreteSubset
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Independence.Integration
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G4CMeasLusin
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.MarkovHit
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.Deriv.Shift
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.SWCoreN2Main
import Mathlib.Order.Filter.AtTopBot.Finset
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.FibreGaussMaxMain
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UnitInterval
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWFarDefs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWFarSideCross
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWBeurlingMain
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.JordanChord
import Mathlib.Data.NNRat.Encodable
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Connected.LocallyConnected
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.Floor
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.Analysis.Calculus.ContDiff.Defs
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Analysis.Complex.Order
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Harmonic.Analytic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T6 (R18-AREAREAD), part 1: the area read from the masked data

Sheffield, arXiv:1012.4797, p. 17: "both `h` and `η` are determined by the pair" of surfaces cut
out by `η`; in particular the quantum area of the pieces is a function of the field **off the
curve** (the curve carries no area, p. 48). Here:

* `readOffField d`: the field sample read from masked data `d` (`E6.FullData`), using only the
  circle coordinates that stay off the curve `curveSel d.2` (a measurable function of `d`,
  `measurable_readOffField`);
* `areaOfData γ d`: the local quantum area of `readOffField d` on `ℍ ∖ curve` (`qAreaMeasureOn`,
  A17: a vague limit tested only on functions supported in `ℍ ∖ curve`; it is concentrated on
  `ℍ ∖ curve`, i.e. extended by `0` on the curve);
* `areaOfData_offData`: for a configuration whose field has a global area limit `μ` on `ℍ`,
  `areaOfData γ (offData x) = μ|_{ℍ ∖ curve}`; with zero area of the curve it is `μ`
  (`areaOfData_offData_eq`).

The locality step is the circle-agreement rule of the local area measure
(`Prop16Asm.qAreaMeasureOn_eq_of_circAgree`) plus uniqueness of local vague limits. Own elementary
bookkeeping (no published proof is needed: this is the measurability/locality content of
"determined by the pair").
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm CoordsFull

/-! ## Measurability of the read field -/

/-! ## The read field agrees with the field off the curve -/

/-! ## Identification with the true area -/

theorem isVagueLimitOn_restrict_R18 {U U' : Set ℂ} (hU' : IsOpen U') (hUU : U' ⊆ U)
    {νs : ℕ → Measure ℂ} {μ : Measure ℂ} (h : IsVagueLimitOn U νs μ) :
    IsVagueLimitOn U' νs (μ.restrict U') := by
  obtain ⟨h0, hK, ht⟩ := h
  refine ⟨by rw [Measure.restrict_apply' hU'.measurableSet]; simp, fun K hKc hKU =>
    (Measure.restrict_apply_le _ _).trans_lt (hK K hKc (hKU.trans hUU)), fun f hf hfc hfU => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h' => ht (hfU h')]
  exact ht f hf hfc (hfU.trans hUU)

end R18
end QuantumZipper
