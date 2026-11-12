/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.XiQBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Lemma25
import LatticeProb.Bonanno.LQGMetric.Papers.DG.ExpCompare
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Analysis.DimAlgebra
import LatticeProb.Bonanno.LQGDimension.Assembly.Theorem11
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

/-- `ξQ = 1 − λ` with `λ = 1 − 2/d − γ²/(2d)` (DG:704–716). -/
lemma xiGamma_mul_Q {γ : ℝ} (hγ : 0 < γ) : xiGamma γ * Q γ = 1 - dgLambda γ := by
  have hd := (dGamma_pos γ).ne'
  unfold xiGamma Q dgLambda
  field_simp
  ring

/-- A circle-average process of the normalized whole-plane GFF exists. -/
lemma exists_circleAvgProcess : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (hc : ℝ → ℂ → Ω → ℝ), LQGDimension.IsGFFCircleAverage hc P := by
  obtain ⟨Ω, _, P, h, _, hh⟩ := GFFExist.exists_wholePlaneGFF
  obtain ⟨H, hH, -⟩ := CircleAvg.exists_isGFFCircleAverage hh
  exact ⟨Ω, inferInstance, P, H, hH⟩

/-- Process-level monotonicity: for `γ₁, γ₂ ∈ (0,2)` with `ξ₁ ≤ ξ₂`, the DG exponents satisfy
`λ₁ + ξ₁²/2 ≤ λ₂ + ξ₂²/2` (DG eqn-exponent-mono, from DG Lemma 2.5 and Thm 1.5). -/
theorem dgLambda_add_le (hDG : DGThm1_5) {γ₁ γ₂ : ℝ} (h1 : 0 < γ₁) (h1' : γ₁ < 2) (h2 : 0 < γ₂)
    (h2' : γ₂ < 2) (hle : xiGamma γ₁ ≤ xiGamma γ₂) :
    dgLambda γ₁ + xiGamma γ₁ ^ 2 / 2 ≤ dgLambda γ₂ + xiGamma γ₂ ^ 2 / 2 := by
  obtain ⟨Ω, _, P, hc, hG⟩ := exists_circleAvgProcess
  have := hG.isProbabilityMeasure
  have hξ := xiGamma_pos h1
  have hG1 := isGFFCircleAverage_fstCA hG
  have hG2 := isGFFCircleAverage_coupledCA hG hξ hle
  exact exponent_le_of_coupling_bound (μ := P.prod P)
    (X := fun δ p => LQGDimension.lfppDistance (xiGamma γ₁) (fun z => fstCA hc δ z p))
    (Xt := fun δ p => LQGDimension.lfppDistance (xiGamma γ₂)
      (fun z => coupledCA (xiGamma γ₁) (xiGamma γ₂) hc δ z p))
    (fun δ hδ p => LQGDimension.LowerAsm.lfppDistance_pos _ (hG1.continuous δ hδ p))
    (fun δ hδ p => LQGDimension.LowerAsm.lfppDistance_pos _ (hG2.continuous δ hδ p))
    (isLFPPExponent_of_dgThm1_5 hDG h1 h1' hG1) (isLFPPExponent_of_dgThm1_5 hDG h2 h2' hG2)
    (dg_lemma25 hG hξ hle)

/-- DEC-A node **DIM.S-chi-le-2** (decision D12, D-A1 step 1; open): `χ ≤ 2`, i.e. `d_γ ≥ 1`,
for every `γ ∈ (0,2)`. DEC-A's proof is a first-moment covering argument for DZZ's Liouville graph
distance (DZZ:740–746 with Markov in place of KPZ); it needs the first moment
`E μ_h(A) ≤ |A|` of `QuantumZipper.qAreaMeasureOn`, not yet available. -/
def ChiLeTwo : Prop := ∀ γ : ℝ, 0 < γ → γ < 2 → chiDZZ γ ≤ 2

lemma one_le_dGamma (hchi : ChiLeTwo) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 1 ≤ dGamma γ := by
  unfold dGamma
  rw [le_div_iff₀ (chiDZZ_pos γ), one_mul]
  exact hchi γ hγ hγ2

/-- **GM.S2.5** (GM l. 1056, `Blueprint.GMXiQBound`) by route B (decision D12), from DG Thm 1.5
and the crude bound `χ ≤ 2` (DEC-A node DIM.S-chi-le-2). -/
theorem gmXiQBound_of_dgThm1_5 (hDG : DGThm1_5) (hchi : ChiLeTwo) : Blueprint.GMXiQBound := by
  have hd1 : ∀ γ : ℝ, 0 < γ → γ < 2 → 1 ≤ dGamma γ := fun γ h h' => one_le_dGamma hchi h h'
  intro γ hγ hγ2
  obtain ⟨Ω, _, P, hc, hG⟩ := exists_circleAvgProcess
  set ξ := xiGamma γ
  have hξ : 0 < ξ := xiGamma_pos hγ
  have hA := LQGDimension.theorem11.1
  have haS : 0 < LQGDimension.aStar := hA.2.2.1
  have hLA := LQGDimension.lambdaAsymptotics_of hA LQGDimension.prop12Upper
    LQGDimension.prop12Lower
  have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
  set η := LQGDimension.aStar / Real.log 16 / 2
  have hη : 0 < η := by positivity
  obtain ⟨ξ₀, hξ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hLA Ω P hc hG η hη)
  have hξ₀' : 0 < ξ₀ := hξ₀
  obtain ⟨g0, g2, gξ, gξ₀⟩ := Analysis.auxGamma_spec hξ hξ₀'
  set γ' := min (min ξ ξ₀) 1 / 2
  have hξ'0 : 0 < xiGamma γ' := xiGamma_pos g0
  have hξ'γ : xiGamma γ' ≤ γ' := div_le_self g0.le (hd1 γ' g0 g2)
  have hlam' := hsub ⟨hξ'0, hξ'γ.trans_lt gξ₀⟩ (dgLambda γ')
    (isLFPPExponent_of_dgThm1_5 hDG g0 g2 hG)
  have hpos : 0 < dgLambda γ' := by
    have hp : 0 < xiGamma γ' ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hξ'0 _
    rw [abs_le] at hlam'
    have : η ≤ dgLambda γ' / xiGamma γ' ^ (4 / 3 : ℝ) := by
      have : LQGDimension.aStar / Real.log 16 = 2 * η := by ring
      linarith [hlam'.1]
    have := (le_div_iff₀ hp).1 this
    nlinarith
  have hmono := dgLambda_add_le hDG g0 g2 hγ hγ2 (hξ'γ.trans gξ.le)
  rw [xiGamma_mul_Q hγ]
  have : 0 ≤ xiGamma γ' ^ 2 / 2 := by positivity
  linarith

end DG
end LQGMetric
