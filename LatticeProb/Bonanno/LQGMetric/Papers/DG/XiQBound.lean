/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.XiQBound at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Basic.ENNReal.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Bounded
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Logic.Equiv.List
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.MetricSpace.Thickening
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Adapter
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Lemma25Gauss
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LatticeProb.Bonanno.LQGDimension.Blueprint.Gaussian
import LatticeProb.Bonanno.LQGDimension.Statement.Defs
import Mathlib.Analysis.Subadditive
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.Gaussian.MaxInequality
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import LatticeProb.Bonanno.LQGDimension.LFPP.OscillationAux
import LatticeProb.Bonanno.LQGDimension.LFPP.HeatKernel
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1
import Mathlib.Data.Int.Log
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms
import LatticeProb.Bonanno.LQGDimension.LFPP.PolygonRiemann
import Mathlib.Algebra.Order.Group.CompleteLattice
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.SubGaussian

/-!
# DG exponent monotonicity (DG.S2-mono) and GM's `ξQ − 1 − ξ²/2 < 0` (GM.S2.5, route B)

* `dg_exponent_mono` (DG eqn-exponent-mono, `metric-comparison-final.tex` l. 770–776): "By
  Theorem 1.5 and Lemma 2.5, for `γ₁, γ₂ ∈ (0,2)`, `γ₁/d_{γ₁} ≤ γ₂/d_{γ₂}` ⇒
  `1 − 2/d_{γ₁} − γ₁²/(2d_{γ₁}) + γ₁²/(2d_{γ₁}²) ≤ 1 − 2/d_{γ₂} − γ₂²/(2d_{γ₂}) + γ₂²/(2d_{γ₂}²)`".
  Proof as in DG: DG Lemma 2.5 (`Lemma25.lean`) on a circle-average process (which exists:
  `GFFExist.exists_wholePlaneGFF` and the bridge `CircleAvg.exists_isGFFCircleAverage`), DG Thm 1.5
  via the adapter (`Adapter.lean`) at both parameters, and `exponent_le_of_coupling_bound`.
* `gmXiQBound_of_dgThm1_5`: GM l. 1056 "`ξQ − 1 − ξ²/2 < 0`" (`Blueprint.GMXiQBound`) by route B
  of decision D12 (`decisions/DEC-A.md` D-A1 steps 1–5): LQGDimension's proved
  `Blueprint.LambdaAsymptotics` (`lambdaAsymptotics_of theorem11.1 prop12Upper prop12Lower`) gives
  `λ(ξ′) > 0` at a small auxiliary `γ′`, and monotonicity transfers it to `γ`. The crude bound
  `χ ≤ 2` (DEC-A node DIM.S-chi-le-2, `ChiLeTwo`) is an explicit hypothesis here (not yet proved).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DG

lemma chiDZZ_pos (γ : ℝ) : 0 < chiDZZ γ := by
  unfold chiDZZ
  split_ifs with h
  · exact h.choose_spec.1
  · norm_num

lemma dGamma_pos (γ : ℝ) : 0 < dGamma γ := div_pos two_pos (chiDZZ_pos γ)

lemma xiGamma_pos {γ : ℝ} (hγ : 0 < γ) : 0 < xiGamma γ := div_pos hγ (dGamma_pos γ)

end DG
end LQGMetric
