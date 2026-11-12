/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.WedgeRC3All2Basic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeShiftHit
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
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
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.Basic.ENNReal.Basic
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
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Analysis.Calculus.MeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.ZoomRadialFinal
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13
import Mathlib.Analysis.Complex.PhragmenLindelof
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Real.Pi.Bounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm
import Mathlib.Logic.Equiv.List
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
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
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeAddConstLat
import LatticeProb.Bonanno.QuantumZipper.Proofs.Wire5

/-!
Deterministic input for `F1.WedgeRC3AllStmt` on folded circles through `0`.

Let `g : ℝ → ℝ` be measurable, continuous on `(0, ∞)`, with `|g t| ≤ C (1 − log t)` on `(0, 1]`,
and `p = g ∘ ‖·‖` (`rp g`). Then

* `continuous_smoothFun_rp`: the circle average `c ↦ ∫ p d fc(c, r)` is continuous on all of `ℂ`
  (also at centres `c` with `‖c‖ = r`, where the circle passes through the singularity);
* `tendsto_integral_smoothFun_rp`: for every folded circle `fc(w, ρ)` (also through `0`),
  `∫∫ p d fc(u, 2^{-k}) d fc(w, ρ)(u) → ∫ p d fc(w, ρ)`.

Route (**own elementary argument**, AGENT_GUIDE cost rule; no source was searched for beyond the
repository, the statement being a routine truncation estimate). Truncate `p` at modulus `δ = s²`
(`rpT g δ = g (max ‖·‖ δ)`, continuous on `ℂ`); the error is bounded pointwise by
`8C (log max(s, ‖v‖) − log ‖v‖)` (`abs_rp_sub_rpT_le`). The only external input is the classical
circle mean of the logarithm `∫ log ‖v‖ d fc(c, r) = log max(r, ‖c‖)`
(`CoordReg.integral_log_norm_foldedCircle`, the mean value property of `log |·|`), which makes the
smoothed error bound `smoothFun (Ls s) c r − log max(r, ‖c‖)` continuous in `(c, r)` and gives,
by dominated convergence, that it tends to `0` as `s → 0` (`tendsto_integral_Ls_sub`). An
abstract ε/3 argument (`tendsto_of_approx`) concludes.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1
namespace RC3Two

/-! ## 0. An abstract approximation lemma -/

/-! ## 1. Radial profiles, truncations and the logarithmic error bound -/

/-- The radial profile `g ∘ ‖·‖`. -/
def rp (g : ℝ → ℝ) : ℂ → ℝ := fun z => g ‖z‖

variable {g : ℝ → ℝ} {C : ℝ}

theorem nonneg_of_bd (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) : 0 ≤ C := by
  have := hbd 1 one_pos le_rfl
  rw [Real.log_one, sub_zero, mul_one] at this
  exact (abs_nonneg _).trans this

/-! ## 2. Continuity of the circle average of the profile -/

/-! ## 3. Vanishing circle smoothing on a folded circle -/

end RC3Two
end F1
end QuantumZipper
