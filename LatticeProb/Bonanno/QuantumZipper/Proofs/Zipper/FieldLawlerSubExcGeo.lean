/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WeldingUniqueness
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import Mathlib.MeasureTheory.Integral.Prod
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.TietzeExtension
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.Complex.ExponentialBounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Real.Pointwise
import Mathlib.Logic.Equiv.List
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Increments
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Convex
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdrySurj
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoJaniszewski
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.Compact
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExt
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Semicontinuity.Basic
import LatticeProb.Bonanno.QuantumZipper.Blueprint.ComplexAnalysis
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CarLengthArea
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeDistortion
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoSep
import Mathlib.Topology.MetricSpace.Sequences
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeCovering
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.PathLaw
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
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
import Mathlib.Analysis.SpecificLimits.Basic
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
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
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaLogSing
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.SetAlgebra
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedLocal
import Mathlib.MeasureTheory.Function.UniformIntegrable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.ZoomRadialFinal
import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.Prop16MeasArea
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.Instances.NNReal.Lemmas
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WedgeRC3All2Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnifSWGaussRatio
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.AbsMax
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWFarDefs
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-EXCLOWER: transport of crosscuts and harmonic measures by the similarity `flSim σ m`

For `σ = ±1`, `m > 0`, the map `flSim σ m : z ↦ (σ Re z + i Im z)/m` is a homeomorphism of `ℂ`
onto itself mapping `ℍ` onto `ℍ` and bounded sets to bounded sets; a harmonic function composed
with its inverse (`w ↦ m w` or `w ↦ −m conj w`) is harmonic. Hence it carries a crosscut `η` to
the crosscut `flSim σ m ∘ η`, the unbounded component `H_η` onto `H_{flSim ∘ η}`, and the harmonic
measure `h` of `η` in `H_η` to the harmonic measure `h ∘ flSim σ m⁻¹` (conformal invariance of
harmonic measure; `flSim` is conformal or anticonformal). Also: reversing the parameter of a
crosscut swaps its endpoints and keeps its point set. Own elementary proofs of these standard
facts (cost rule of AGENT_GUIDE).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- A harmonic function composed with complex conjugation is harmonic. -/
lemma fl_harmonicAt_conj {g : ℂ → ℝ} {w : ℂ} (hg : InnerProductSpace.HarmonicAt g (conj w)) :
    InnerProductSpace.HarmonicAt (fun u => g (conj u)) w := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (InnerProductSpace.isOpen_setOfPred_harmonicAt (f := g)) _ hg
  obtain ⟨F, hF, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := g)
      (z := conj w) (R := r) (fun y hy => hball hy)
  have hmem : ∀ u ∈ ball w r, conj u ∈ ball (conj w) r := fun u hu => by
    rw [mem_ball, dist_eq_norm, ← map_sub, Complex.norm_conj, ← dist_eq_norm]; exact hu
  have hG : DifferentiableOn ℂ (conj ∘ F ∘ conj) (ball w r) := by
    intro u hu
    have hd := ((hF _ (hmem u hu)).differentiableAt.hasDerivAt).conj_conj
    rw [Complex.conj_conj] at hd
    exact hd.differentiableAt.differentiableWithinAt
  have hGa : AnalyticAt ℂ (conj ∘ F ∘ conj) w :=
    hG.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hGa.harmonicAt_re
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with u hu
  simp only [Function.comp_apply, Complex.conj_re]
  exact hFeq (hmem u hu)

section Transport

variable {σ m : ℝ} (hσ : σ = 1 ∨ σ = -1) (hm : 0 < m)

end Transport

end FieldLawler
end QuantumZipper
