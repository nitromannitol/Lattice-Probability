/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P21 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (T20, T20C, T20D). -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector
import LatticeProb.Bonanno.LQGMetric.LFPP.PathPiece
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePsi
import Mathlib.Analysis.Complex.ExponentialBounds
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.PSeries
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationVector
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Probability.CondVar
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.LQGMetric.Topo.RectMeet
import LatticeProb.Bonanno.LQGMetric.Perc.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import LatticeProb.Bonanno.LQGMetric.Perc.DualityMain
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Basic.ENNReal.Real
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.KolmN
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Topology.Bases
import Mathlib.Analysis.Complex.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.GermZeroOne
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import Mathlib.Topology.Path
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualExistence
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqExist
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Basic
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.LQG.Local

/-!
DDDF = arXiv:1904.08021, `tightness.tex` l. 972–1018 (`Prop:CondSatisfied`), from (5.54)
(`eq:DGlowerBound`, l. 1004–1010; DG Prop 3.17 + DGo Prop 3.3), taken as the hypothesis
`S6Eq5_54`.

Proof as DDDF's: Steps 1–3 pathwise (`S6.ratio_pathwise`), then Hölder (here one generalized
Hölder inequality with the four weights `1/r, 1/(3s), 1/(3s), 1/(3s)`, `α = r = ρ`,
`ρ² ξ = (ξ+2)/2 < 2`, instead of Hölder + Cauchy–Schwarz) with the moment bounds (2.11)
(`prop2_expMoment_int`), Prop 5 (`expMoment_XAB_shift`), (2.17) (`prop3_expMoment_shift`, with
`ε = 1/8`) and Cor 17 (`S6.invMoment_L11`); Step 4 is (5.54) with `ζ = ξ(Q−2)/2`; Step 5 is the
asymptotics (`T20C.asymp`). The parameters of `ψ` are `r₀ = 1/12`, `ε₀ = 1/4` (`S6.psiQ₁`), so
that `PsiSmall` and `ε₀ < 1/2` (needed by Theorem 20) hold. `ξ < 2` comes from `d_γ ≥ 1`
(`DG.one_le_dGamma`, `DG.chiLeTwo`), so `ξ ≤ γ < 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

namespace S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end S6

end DDDF
end LQGMetric
