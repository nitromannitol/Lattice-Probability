/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1PolarPt at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarSwap
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Exp
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm
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
# DFGPS Lemma 2.1: the polar formula at a fixed `(ε, z)`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:715–722: "The functions
`w ↦ ψ_ε(z−w)` and `w ↦ p_{ε²/2}(z,w)` are each radially symmetric about `z` … Using the circle
average process we may therefore write in polar coordinates
`g*_ε(z) = (2/ε²) ∫_0^∞ r g_r(z) e^{−r²/ε²} dr`, `ĝ*_ε(z) = (2/ε²) ∫_0^{ε^{1/2}} r g_r(z) ψ_ε(r) e^{−r²/ε²} dr`."

* `Lem2_1RadialPairing` (open node): for a test function `φ` radial about `z`, a.s.
  `⟨g, φ⟩ = ∫_0^∞ 2π r φ(z + r) g_r(z) dr` (polar coordinates with the circle averages).
* `lem2_1PolarPoint_of : Lem2_1RadialPairing → Lem2_1PolarPoint`: apply it to the radial test
  functions `p_s(z,·)ρ_n(· − z) − ψ_ε(z − ·)p_s(z,·)`, swap the cutoffs
  (`ae_tendsto_heatTrunc_sub_radTrunc`) and let `n → ∞` by dominated convergence (Lemma 2.2 bound).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace LQGMetric.DFGPS

open LFPP

/-- **Pairing with a radial test function** (DFGPS T:715–717): for a whole-plane GFF `g`, a jointly
continuous version `H` of its circle-average process, and a test function `φ` radial about `z`,
a.s. `⟨g, φ⟩ = ∫_0^∞ 2π r φ(z + r) H(r, z) dr`. Open node. -/
def Lem2_1RadialPairing.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ),
    IsWholePlaneGFF g P → IsCircleAvgVersion g P H →
    ∀ (z : ℂ) (φ : TestC), (∀ w : ℂ, φ w = φ (z + ((‖w - z‖ : ℝ) : ℂ))) →
    ∀ᵐ ω ∂P, g ω φ = ∫ r in Ioi (0 : ℝ), 2 * Real.pi * r * φ (z + (r : ℂ)) * H r z ω

lemma heatKernel_radial (s : ℝ) (z w : ℂ) :
    heatKernel s z w = heatKernel s z (z + ((‖w - z‖ : ℝ) : ℂ)) := by
  unfold heatKernel
  rw [show z - (z + ((‖w - z‖ : ℝ) : ℂ)) = -((‖w - z‖ : ℝ) : ℂ) by ring, norm_neg,
    Complex.norm_real, norm_norm, norm_sub_rev]

lemma heatKernel_add_real (s : ℝ) (z : ℂ) (r : ℝ) :
    heatKernel s z (z + r) = (2 * Real.pi * s)⁻¹ * Real.exp (-r ^ 2 / (2 * s)) := by
  unfold heatKernel
  rw [show z - (z + (r : ℂ)) = -(r : ℂ) by ring, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

lemma locBump_neg_real {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    locBump ε hε (-(r : ℂ)) = locBump ε hε (r : ℂ) := by
  rw [locBump_radial ε hε (-(r : ℂ)), locBump_radial ε hε (r : ℂ), norm_neg]

/-- the radial test function `p_s(z,·)ρ_n(· − z) − ψ_ε(z − ·)p_s(z,·)` -/
def polarTest (ε : ℝ) (hε : 0 < ε) (z : ℂ) (n : ℕ) : TestC :=
  radTrunc (ε ^ 2 / 2) z n - locTest ε hε z

lemma polarTest_apply (ε : ℝ) (hε : 0 < ε) (z : ℂ) (n : ℕ) (w : ℂ) :
    polarTest ε hε z n w = heatKernel (ε ^ 2 / 2) z w * radCut n (w - z) -
      locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w := rfl

lemma polarTest_radial (ε : ℝ) (hε : 0 < ε) (z : ℂ) (n : ℕ) (w : ℂ) :
    polarTest ε hε z n w = polarTest ε hε z n (z + ((‖w - z‖ : ℝ) : ℂ)) := by
  rw [polarTest_apply, polarTest_apply, ← heatKernel_radial, add_sub_cancel_left,
    show z - (z + ((‖w - z‖ : ℝ) : ℂ)) = -((‖w - z‖ : ℝ) : ℂ) by ring, locBump_neg_real,
    radCut_radial n (w - z), locBump_radial ε hε (z - w), norm_sub_rev]

lemma polarTest_add_real (ε : ℝ) (hε : 0 < ε) (z : ℂ) (n : ℕ) (r : ℝ) :
    2 * Real.pi * r * polarTest ε hε z n (z + r) =
      2 / ε ^ 2 * (r * (radCut n (r : ℂ) - locBump ε hε (r : ℂ)) *
        Real.exp (-r ^ 2 / ε ^ 2)) := by
  rw [polarTest_apply, add_sub_cancel_left, show z - (z + (r : ℂ)) = -(r : ℂ) by ring,
    locBump_neg_real, heatKernel_add_real]
  have hε0 : ε ≠ 0 := by
    intro h0; simp [h0] at hε
  have hpi := Real.pi_pos.ne'
  rw [show 2 * (ε ^ 2 / 2) = ε ^ 2 by ring]
  field_simp

/-- **The polar formula at a fixed `(ε, z)`** from the radial pairing formula. -/
theorem lem2_1PolarPoint_of.{u} (HR : Lem2_1RadialPairing.{u}) : Lem2_1PolarPoint.{u} := by
  intro Ω _ P g H hg hH ε hε z
  set s := ε ^ 2 / 2
  have hs : 0 < s := by positivity
  obtain ⟨A, hA, hAb⟩ := lem2_2 hg hH (‖z‖ + 1)
  have hz : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by rw [mem_ball_zero_iff]; linarith
  have hPt : ∀ᵐ ω ∂P, ∀ n : ℕ, g ω (polarTest ε hε z n) =
      ∫ r in Ioi (0 : ℝ), 2 * Real.pi * r * polarTest ε hε z n (z + (r : ℂ)) * H r z ω :=
    ae_all_iff.2 fun n => HR P g H hg hH z _ (polarTest_radial ε hε z n)
  filter_upwards [hg.ae_tendsto_heatMollify ε hε.ne' z, ae_tendsto_heatTrunc_sub_radTrunc hg hs z,
    hPt, hAb (1 / 2) (by norm_num)] with ω h1 h2 h3 h4
  obtain ⟨C, hC⟩ := h4
  set f : ℝ → ℝ := fun r => 2 / ε ^ 2 * (r * H r z ω * (1 - locBump ε hε (r : ℂ)) *
    Real.exp (-r ^ 2 / ε ^ 2))
  -- dominated convergence for the polar integrals
  have hDCT : Tendsto (fun n : ℕ => g ω (polarTest ε hε z n)) atTop
      (𝓝 (∫ r in Ioi 0, f r)) := by
    simp only [h3]
    have hHc : ContinuousOn (fun r => H r z ω) (Ioi 0) :=
      (hH.cont ω).comp (continuous_id.prodMk continuous_const).continuousOn
        fun r hr => ⟨hr, mem_univ _⟩
    refine tendsto_integral_of_dominated_convergence (fun r => 2 / ε ^ 2 * (|C| *
      ((A + r ^ 2 + r) * Real.exp (-(1 / ε ^ 2) * r ^ 2)))) (fun n => ?_)
      (((integrableOn_gaussW A (by positivity)).const_mul _).const_mul _) (fun n => ?_) ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ((continuousOn_const.mul continuousOn_id).mul
        ((polarTest ε hε z n).continuous.comp (continuous_const.add
          Complex.continuous_ofReal)).continuousOn).mul hHc
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr : 0 < r := hr
      rw [polarTest_add_real]
      have hI := radCut_mem_Icc n (r : ℂ)
      have hd : |radCut n (r : ℂ) - locBump ε hε (r : ℂ)| ≤ 1 := by
        have := locBump_nonneg ε hε (r : ℂ); have := locBump_le_one ε hε (r : ℂ)
        rw [abs_le]; constructor <;> linarith [hI.1, hI.2]
      have hFb : |H r z ω| ≤ |C| * (A / r + r + 1) := by
        have hm := max_log_le hA.le hr
        have hm1 : (1 : ℝ) ≤ max (max (A * Real.log (1 / r))
            (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := le_max_right _ _
        calc |H r z ω| ≤ C * max (max (A * Real.log (1 / r))
              (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := hC r hr z hz
          _ ≤ |C| * max (max (A * Real.log (1 / r))
              (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
          _ ≤ |C| * (A / r + r + 1) := mul_le_mul_of_nonneg_left hm (abs_nonneg C)
      have he : Real.exp (-r ^ 2 / ε ^ 2) = Real.exp (-(1 / ε ^ 2) * r ^ 2) := by
        congr 1; ring
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 / ε ^ 2), abs_of_pos hr,
        abs_of_pos (Real.exp_pos _), he]
      set E := Real.exp (-(1 / ε ^ 2) * r ^ 2)
      calc 2 / ε ^ 2 * (r * |radCut n (r : ℂ) - locBump ε hε (r : ℂ)| * E) * |H r z ω|
          = 2 / ε ^ 2 * (r * |radCut n (r : ℂ) - locBump ε hε (r : ℂ)| * E * |H r z ω|) := by
            ring
        _ ≤ 2 / ε ^ 2 * (r * 1 * E * (|C| * (A / r + r + 1))) := by gcongr
        _ = 2 / ε ^ 2 * (|C| * ((A + r ^ 2 + r) * E)) := by
            field_simp
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈r⌉₊] with n hn
      have hrn : r ≤ (n : ℝ) + 1 := by
        have := (Nat.le_ceil r).trans (Nat.cast_le.2 hn); linarith
      have hr0 : (0 : ℝ) < r := hr
      rw [polarTest_add_real, radCut_eq_one n (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hrn)]
      simp only [f]; ring
  -- assemble
  have hsum : Tendsto (fun n : ℕ => (g ω (heatTrunc s z n) - g ω (radTrunc s z n)) +
      g ω (polarTest ε hε z n)) atTop (𝓝 (0 + ∫ r in Ioi 0, f r)) := h2.add hDCT
  have hlim : Tendsto (fun n : ℕ => g ω (heatTrunc s z n) - locMollify ε hε (g ω) z) atTop
      (𝓝 (heatMollify ε (g ω) z - locMollify ε hε (g ω) z)) := h1.sub_const _
  have e : (fun n : ℕ => (g ω (heatTrunc s z n) - g ω (radTrunc s z n)) +
      g ω (polarTest ε hε z n)) = fun n : ℕ => g ω (heatTrunc s z n) -
        locMollify ε hε (g ω) z := by
    funext n
    simp only [polarTest, map_sub, locMollify]
    ring
  rw [e, zero_add] at hsum
  rw [tendsto_nhds_unique hlim hsum, integral_const_mul]

end LQGMetric.DFGPS
