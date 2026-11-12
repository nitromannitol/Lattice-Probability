/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.GFF at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.Field
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.MarkovWeyl3
import LatticeProb.Bonanno.LQGMetric.Field.MarkovExt
import LatticeProb.Bonanno.LQGMetric.Field.MarkovNorm
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Finsupp.Encodable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Algebra.QuadraticDiscriminant
import LatticeProb.Bonanno.LQGMetric.Field.ExistKolm
import LatticeProb.Bonanno.LQGMetric.Field.ExistRect
import LatticeProb.Bonanno.LQGMetric.Field.ExistKerId
import LatticeProb.Bonanno.LQGMetric.Field.ExistSFub2
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepCirc
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.ThinAnnulus
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UnitInterval
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC
import LatticeProb.Bonanno.LQGMetric.Metric.LengthSpace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Tietze
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Compactification.OnePoint.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Rat.Denumerable
import Mathlib.Topology.Instances.AddCircle.Real
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGaussLim
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryLaw
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Order.Floor
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Regularity
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import Mathlib.Probability.Moments.Basic
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSScaling
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import Mathlib.Algebra.Order.Field.GeomSum
import LatticeProb.Bonanno.LQGMetric.Metric.SetDist
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightBlueprint
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Meas
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepZB
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Process.Filtration
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Probability.ConditionalExpectation
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import Mathlib.Topology.TietzeExtension
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector
import LatticeProb.Bonanno.LQGMetric.LFPP.PathPiece
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsi
import Mathlib.Analysis.Complex.ExponentialBounds
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Algebra.Group.Pointwise
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import Mathlib.Data.Nat.Log
import Mathlib.Basic.ENNReal.Real
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Topology.Bases
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import Mathlib.Probability.HasLaw
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.PSeries
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.LQGMetric.Perc.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.Complex.Isometry
import LatticeProb.Bonanno.LQGMetric.Perc.DualityMain
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryExt
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationVector
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.MeasureTheory.Integral.ExpDecay
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquare2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Second
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareTheta
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatBound
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Analysis.SpecialFunctions.Exp
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatLaw
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import LatticeProb.Bonanno.LQGMetric.Metric.WeylBasic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen6
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain
import Mathlib.MeasureTheory.Integral.Indicator
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Basic
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.CondDistrib
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Centre
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Martingale.Convergence
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeat

/-!
* `ofFunOn U f : FieldOn U`: the distribution `φ ↦ ∫ φ f` on `U` (mathlib `Distribution.ofFun`;
  junk `0` when `f` is not locally integrable on `U`), the `U`-version of LQGMetric's `ofCont`.
* `IsGFFBoundary U 𝔥 X P`: `X` is a GFF on `U` with (random) harmonic boundary data `𝔥`, i.e.
  `X|_U − 𝔥` is a zero-boundary GFF on `U` in the sense of `LQGMetric.IsZeroBoundaryGFF`
  (Sheffield, *Gaussian free fields for mathematicians*, math/0312099 §2; IG1 §1 / §3.2).
* `exists_isGFFBoundary`: existence for deterministic harmonic data `𝔥` on an open set `U`
  missing some circle, when the zero extension of `𝔥` is locally integrable on `ℂ`
  (e.g. bounded `𝔥`, `exists_isGFFBoundary_of_bounded`). Construction: LQGMetric's whole-plane
  GFF `h` (`GFFExist.exists_wholePlaneGFF`), normalized on the circle, Markov decomposition
  `LQGMetric.CONF.markov_harmPart_dec` (LM Lemma 2.1 transported) gives the zero-boundary part
  `h − G`; add the extension by zero of `𝔥`.

* `NonPolarCompl U`: planar Brownian motion started at any
  point of `U` exits `U` almost surely (the harmonically nontrivial boundary condition of IG4). `IsGFFBoundary U` is only meaningful under this hypothesis (see its
  docstring).

The expression `restrictTo U (X − ofFunOn U 𝔥)` does not typecheck (`ofFunOn U 𝔥` lives on `U`); we use `restrictTo U X − ofFunOn U 𝔥`. Since a
`Field` is a distribution on all of `ℂ`, a field with boundary data `𝔥` exists only when `𝔥` (on `U`)
is the restriction of a distribution on `ℂ`; our existence theorem assumes local integrability
of the zero extension.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions

namespace MatedCRTHarmonic.MoTPort

open LQGMetric

/-- the distribution `φ ↦ ∫ φ f` on the open set `U` (junk `0` if `f` is not locally integrable
on `U`) -/
def ofFunOn (U : Opens ℂ) (f : ℂ → ℝ) : FieldOn U := Distribution.ofFun U f volume ⊤

/-- the distribution on `ℂ` of a function (junk `0` if not locally integrable) -/
def ofFunC (f : ℂ → ℝ) : Field := Distribution.ofFun ⊤ f volume ⊤

variable {Ω : Type*} [MeasurableSpace Ω]

namespace GFFBdry

end GFFBdry

open GFFBdry

end MatedCRTHarmonic.MoTPort
