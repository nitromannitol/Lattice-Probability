/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.SWCoreN2Chain at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.CameronMartin
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
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FiniteArea
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaLogSing
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.NonVacuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WeldingUniqueness
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegKolm
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnzipInvariance
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
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
import Mathlib.MeasureTheory.Function.JacobianOneDim
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Topology.PartitionOfUnity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Polynomial.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeBasic
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Int
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
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Real.Pi.Bounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedLocal
import Mathlib.MeasureTheory.Function.UniformIntegrable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Probability.Kernel.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscTV
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Constructions.Cylinders
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.G3Core
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.Prop16MeasArea
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.UnifSWGaussRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (1): small Gaussian families with a scale-relative modulus are uniformly small a.s.

Task SWC-N (`handoff/SW-CORE.md` §5), the chaining + Borel–Cantelli step of the distortion core,
for families indexed by a bounded countable set `D ⊂ ℝ^d` (sup norm). For each scale
`k` let `Z k θ` (`θ ∈ D`) be a centred Gaussian process with

* `Var (Z k θ) ≤ V · r_k^{β₀}`                              (SW (3.20): pushed vs round),
* `Var (Z k θ − Z k θ') ≤ L² (‖θ − θ'‖ / r_k)^β` for `‖θ − θ'‖ ≤ r_k²`  (the modulus),

`r_k = 2^{-k}`. Then almost surely, for every `η > 0`, eventually in `k`, `|Z k θ| ≤ η` for all
`θ ∈ D` (`swcn2_ae_eventually_small`).

Proof (Sheffield–Wang, arXiv:1605.06171, Lemma 3.5 and the Borel–Cantelli step after (3.23),
p. 16): cover `D` by `≲ 4^{kd}` sup-norm boxes of side `r_k²`; in each box the supremum of
`Z − Z(i₀)` has exponential moments `≤ exp(t m + π²/8 t² σ²)` by Dudley chaining + Borell–TIS
(`RegUnif.swg_exp_sup_le`) with `m ≲ L r_k^{β/2}`, `σ² ≤ L² r_k^β`; the value at the box
representative has Gaussian exponential moments (`RegUnif.swg_lintegral_exp_gauss`). With
`t = r_k^{-β/2}` (resp. `r_k^{-β₀/2}`) and Markov's inequality each box contributes
`≲ exp(−(η/3) 2^{kβ/2})`, which beats the box count `4^{kd}` (`swcn2_summable`); Borel–Cantelli.
Own assembly of cited tools.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif

/-- `A^k e^{−c B^k}` is summable for `B > 1`, `c > 0`. -/
theorem swcn2_summable {A c B : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hB : 1 < B) :
    Summable fun k : ℕ => A ^ k * Real.exp (-(c * B ^ k)) := by
  have hB0 : 0 < B := by linarith
  -- choose `j` with `B^j ≥ 2 (A + 1)`
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (2 * (A + 1)) hB
  have hBj : 0 < B ^ j := pow_pos hB0 j
  set q : ℝ := A / B ^ j with hq
  have hq0 : 0 ≤ q := div_nonneg hA hBj.le
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hBj]; linarith
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left ((j.factorial : ℝ) / c ^ j))
  have hx : 0 ≤ c * B ^ k := by positivity
  have hexp := Real.pow_div_factorial_le_exp (c * B ^ k) hx j
  have hpos : 0 < (c * B ^ k) ^ j := by positivity
  have h1 : Real.exp (-(c * B ^ k)) ≤ (j.factorial : ℝ) / (c * B ^ k) ^ j := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    exact hexp
  calc A ^ k * Real.exp (-(c * B ^ k)) ≤ A ^ k * ((j.factorial : ℝ) / (c * B ^ k) ^ j) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hA k)
    _ = (j.factorial : ℝ) / c ^ j * q ^ k := by
        rw [hq, div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]
        field_simp
    _ ≤ _ := le_rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Markov's inequality for an exponential moment bound. -/
theorem swcn2_markov_exp {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {c s : ℝ}
    (hb : ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal (Real.exp c)) :
    P {ω | ENNReal.ofReal (Real.exp s) ≤ f ω} ≤ ENNReal.ofReal (Real.exp (c - s)) := by
  have hs0 : ENNReal.ofReal (Real.exp s) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos s
  refine (meas_ge_le_lintegral_div hf hs0 ENNReal.ofReal_ne_top).trans ?_
  calc (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (Real.exp s)
      ≤ ENNReal.ofReal (Real.exp c) / ENNReal.ofReal (Real.exp s) := by gcongr
    _ = ENNReal.ofReal (Real.exp (c - s)) := by
        rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos s), Real.exp_sub]

/-- **One box**: the supremum over a countable set of a centred Gaussian process relative to a
reference point exceeds `η` with probability `≤ exp(t m + π²/8 t² σ² − t η)`. -/
theorem swcn2_box_tail [IsProbabilityMeasure P] {ι : Type} [Countable ι] {Z : ι → Ω → ℝ} (hZ : IsGaussianProcess Z P)
    (hc : ∀ i, ∫ ω, Z i ω ∂P = 0) (hZm : ∀ i, Measurable (Z i)) {d : ℕ} (p : ι → Fin d → ℝ)
    {L a β σ t η : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hσ0 : 0 ≤ σ) (ht : 0 ≤ t)
    (i₀ : ι) (A : Set ι) (hp : ∀ i ∈ A, ∀ j ∈ A, ‖p i - p j‖ ≤ a)
    (hv : ∀ i ∈ A, ∀ j ∈ A, Var[fun ω => Z i ω - Z j ω; P] ≤ L ^ 2 * ‖p i - p j‖ ^ β)
    (hσ : ∀ i ∈ A, Var[fun ω => Z i ω - Z i₀ ω; P] ≤ σ ^ 2) :
    P {ω | ∃ i ∈ A, η ≤ Z i ω - Z i₀ ω} ≤
      ENNReal.ofReal (Real.exp (t * (fgmChainConst d β * L * a ^ (β / 2)) +
        π ^ 2 / 8 * t ^ 2 * σ ^ 2 - t * η)) := by
  have hmeas : AEMeasurable (fun ω => ⨆ i ∈ A, ENNReal.ofReal (Real.exp (t * (Z i ω - Z i₀ ω))))
      P := by
    refine (Measurable.biSup _ (Set.to_countable A) fun i _ => ?_).aemeasurable
    exact (Real.measurable_exp.comp (((hZm i).sub (hZm i₀)).const_mul t)).ennreal_ofReal
  refine (measure_mono fun ω hω => ?_).trans
    (swcn2_markov_exp hmeas (swg_exp_sup_le hZ hc p hβ hβ1 hL hσ0 ht i₀ A hp hv hσ))
  obtain ⟨i, hi, hle⟩ := hω
  show ENNReal.ofReal (Real.exp (t * η)) ≤ _
  refine le_trans ?_ (le_iSup₂_of_le i hi le_rfl)
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle ht))

/-- **One point**: a centred Gaussian exceeds `η` with probability `≤ exp(Var t²/2 − t η)`. -/
theorem swcn2_point_tail {U : Ω → ℝ} (hU : HasGaussianLaw U P) (hc : ∫ ω, U ω ∂P = 0)
    (hUm : Measurable U) {t η : ℝ} (ht : 0 ≤ t) :
    P {ω | η ≤ U ω} ≤ ENNReal.ofReal (Real.exp (Var[U; P] * t ^ 2 / 2 - t * η)) := by
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (t * U ω))) P :=
    (Real.measurable_exp.comp (hUm.const_mul t)).ennreal_ofReal.aemeasurable
  refine (measure_mono fun ω hω => ?_).trans
    (swcn2_markov_exp hmeas (swg_lintegral_exp_gauss hU hc t).le)
  show ENNReal.ofReal (Real.exp (t * η)) ≤ _
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω ht))

end SWCore
end QuantumZipper
