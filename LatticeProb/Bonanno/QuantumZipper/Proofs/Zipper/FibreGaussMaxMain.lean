/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.FibreGaussMaxMain at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (RegCont). -/
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Convex
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdrySurj
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExt
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Blueprint.ComplexAnalysis
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnzipInvariance
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.MeasureTheory.Integral.Prod
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WeldingUniqueness
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Probability.Kernel.MeasurableIntegral
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Complex.RealDeriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegSwap
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Instances.Real.Lemmas
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Increments
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm
import Mathlib.Analysis.SpecialFunctions.Bernstein
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Topology.PartitionOfUnity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CarLengthArea
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeDistortion
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep
import Mathlib.Topology.MetricSpace.Sequences
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeCovering
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.PathLaw
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Real.Pi.Bounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import Mathlib.MeasureTheory.Function.Floor
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
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Real.Pointwise
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.NonVacuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FiniteArea
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaOffsets
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdryFold
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Polynomial.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscTV
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.Instances.NNReal.Lemmas
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.FibreGaussMaxLaw
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.FibreGaussMaxChain
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FIBRE-GAUSSMAX (3): the finite Gaussian maxima, `FibreGaussMaxStmt κ p` for `p > 0`

For a finite set `F` of tip parameters, add the reference parameter `(0,0)` (whose circle is
`fc(0,1)`, so its coordinate vanishes) and the intermediate parameters `(h.1, g.2)`. The tip
coordinates `X(ν i) - X(fc(0,1))` form a finite centred Gaussian vector, realised as `⟪v i, x⟫`
under a standard Gaussian (`fgmLaw_gram`). Then

* increments: `‖v g - v h‖² ≤ 4 A ‖P g - P h‖^{1/36}` with `A = fgmA κ C` (`fgm_hv`);
* expected maximum (Dudley chaining, Hölder form, `fgmChain_bound`; Adler–Taylor, *Random Fields
  and Geometry*, Thm 1.3.3; Talagrand, *Upper and Lower Bounds for Stochastic Processes*, §2.2):
  `E max ≤ K_ch · 2√A · 2^{1/72}`;
* concentration (Maurey–Pisier form of Borell–TIS, `MaxConc.lintegral_exp_max_le`;
  Pisier 1986, *Probabilistic methods in the geometry of Banach spaces*, Thm 2.2; Adler–Taylor
  Thm 2.1.1): `E e^{t(M - EM)} ≤ e^{π² t² σ²/8}` with `σ² ≤ 4A`;

so `E[(max e^{√κ X(ν i)})^p] ≤ exp(fgmE κ p · (1 + A))` (`fgm_core`), and `A ≤ fgmD κ (1 + C)`
(`fgmA_le`) gives the `K_ε e^{ε C²}` bound for every `ε > 0` (in fact `e^{O(C)}`).
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal RealInnerProductSpace Real

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint KolmD RegSample LQGDimension

/-- Exponential moment of a finite Gaussian maximum from a bound on its expectation. -/
theorem fgm_gauss_exp_le {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (F : Finset ι) (v : ι → E)
    {t σ B : ℝ} (ht : 0 ≤ t) (hσ : ∀ i ∈ F, ‖v i‖ ≤ σ) (hB : vecExpectedMax F v 0 ≤ B) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * ⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i)) ∂stdGaussian E ≤
      ENNReal.ofReal (Real.exp (t * B + π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
  have h := MaxConc.lintegral_exp_max_le F v 0 hσ t
  set EM := vecExpectedMax F v 0
  have e : ∀ x : E, ENNReal.ofReal (Real.exp (t * ⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i)) =
      ENNReal.ofReal (Real.exp (t * ((⨆ i : F, ⟪v i, x⟫ + (0 : ι → ℝ) i) - EM))) *
        ENNReal.ofReal (Real.exp (t * EM)) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  simp_rw [e]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc _ ≤ ENNReal.ofReal (Real.exp (π ^ 2 / 8 * t ^ 2 * σ ^ 2)) *
        ENNReal.ofReal (Real.exp (t * EM)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (t * EM + π ^ 2 / 8 * t ^ 2 * σ ^ 2)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_comm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))

end RegUnif
end QuantumZipper
