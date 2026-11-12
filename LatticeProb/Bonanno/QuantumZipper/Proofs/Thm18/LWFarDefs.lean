/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm18.LWFarDefs at commit fdb5cad; only the module paths of local imports are changed.
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Dynkin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Increments
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.ItoLite.Oscillation
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm11
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.ZeroRegularization
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Path
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeDistortion
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Normed
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CarLengthArea
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.TietzeExtension
import LatticeProb.Bonanno.QuantumZipper.Blueprint.ComplexAnalysis
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
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
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
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
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.HoloLog
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.RMTStep3
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraExt
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdryFold
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.CaraBdrySurj
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.FromThm13
import Mathlib.Analysis.Complex.PhragmenLindelof
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegHarm
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedLocal
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Probability.Kernel.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.ZoomRadialFinal
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
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.StrongMarkov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node LW-FAR: the statement plan for a far-apart two-point estimate

Task LW-FAR-PLAN (plan: `handoff/LW-FAR.md`). The consumer `g4UpTraceNullStmt_of_twoPointFar_q`
(`LWFarQChain.lean`) needs `SLETwoPointFarUnit κ q` for SOME `q > 1` (`0 < κ < 4`). This file fixes
the exact statements of the intermediate nodes of the route chosen in the plan (target exponent
`q = 3/2 − κ/8`); it contains definitions only (no proofs, no hypotheses are assumed anywhere).

Notation (`W` a driver, `t ≥ 0`, `x ∈ H_t = H \ K_t`), following G. Lawler, B. Werness,
*Multi-point Green's functions for SLE and an estimate of Beffara*, Ann. Probab. 41 (2013),
§2.1–2.2 (`literature/1011.3551.pdf`, pp. 4–10):
* `cMap W t x = g_t(x) − W_t = fwdMap W t x` (LW's `Z_t`), `upsilon W t x = Im g_t(x)/|g_t'(x)|` (LW's `Υ_t`,
  `= exp (fwdLogCR W t x)`), `sinArg W t x = Im Z_t/|Z_t|` (LW's `S_t`);
* `Pocket W t w z ρ`: the closed disk `B̄(w, ρ)` disconnects `z` from `∞` in `H_t` (V. Beffara,
  *The dimension of the SLE curves*, Ann. Probab. 36 (2008), §3.1, the quantity `ρ_t`, p. 12).

Sources of the nodes: Beurling estimate (LW Prop 2.1, p. 5; Lawler, *Conformally Invariant
Processes in the Plane*, Thm 3.69, p. 77; Garnett–Marshall, *Harmonic Measure*, Thm III.9.2);
side bound (LW eq. (2), p. 6; Beffara Lemma 6, p. 13); boundary hitting (LW Prop 2.6, p. 10);
fjord/pocket entry (LW Lemmas 4.3–4.5, pp. 23–25, used as in LW Lemmas 4.11–4.12, pp. 29–30;
Beffara Lemma 8, p. 15); conditional one-point estimate (LW Lemma 2.10, p. 12; Beffara Cor 5,
p. 9). The assembly (pocket-product bound and the dyadic sums) is an own simplification of LW
§4.4 that loses a logarithm, which the consumer can afford (see the plan).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- **LWF-2. Boundary hitting estimate** (LW Prop 2.6, p. 10, for a disk about a real point;
exponent `8/κ − 1`). -/
def BdryHitStmt (κ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ x r : ℝ, 0 < r → 2 * r ≤ |x| →
      P {ω | ∃ t : ℝ, 0 ≤ t ∧ ‖sleTrace κ B ω t - x‖ < r} ≤
        ENNReal.ofReal (C * (r / |x|) ^ (8 / κ - 1))

/-- **LWF-4. Beurling estimate for harmonic majorants** (LW Prop 2.1, p. 5; Lawler, CIP,
Thm 3.69; Garnett–Marshall Thm III.9.2 and its corollary), analytic form: a harmonic `h` with
`0 ≤ h ≤ 1` on the component `V` of `D ∩ B(w, ρ)` containing `w`, tending to `0` at the points of
`∂D` inside the disk, where `ℂ \ D` contains a continuum crossing `{d ≤ |x − w| ≤ ρ}`, satisfies
`h(w) ≤ C (d/ρ)^{1/2}`. -/
def BeurlingHarmStmt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (D K : Set ℂ) (w : ℂ) (d ρ : ℝ) (h : ℂ → ℝ),
    IsOpen D → w ∈ D → 0 < d → d ≤ ρ → IsConnected K → Disjoint K D →
    (K ∩ closedBall w d).Nonempty → (K \ ball w ρ).Nonempty →
    InnerProductSpace.HarmonicOnNhd h (connectedComponentIn (D ∩ ball w ρ) w) →
    (∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, 0 ≤ h x ∧ h x ≤ 1) →
    (∀ x₀ ∈ frontier D ∩ ball w ρ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ connectedComponentIn (D ∩ ball w ρ) w, dist x x₀ < δ → h x ≤ ε) →
    h w ≤ C * (d / ρ) ^ (1 / 2 : ℝ)

end LWFar
end Thm18Asm
end QuantumZipper
