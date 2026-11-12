/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P21 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Ratio
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Mom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Max
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CMain
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C17
import LatticeProb.Bonanno.LQGMetric.Papers.DG.BallMass
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
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
# DDDF Proposition 21: `ξ = γ/d_γ` satisfies Condition (T) (task P2-DDDF6c)

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

open WhiteNoise SupTail T20 T20C T20D

namespace S6

/-- the parameters `r₀ = 1/12`, `ε₀ = 1/4` of `ψ` -/
def psiQ₁ : PsiParams where
  cut := Classical.choice exists_psiCutoff
  r₀ := 1 / 12
  ε₀ := 1 / 4
  r₀_pos := by norm_num
  ε₀_pos := by norm_num

theorem psiSmall_psiQ₁ : PsiSmall psiQ₁ := by
  intro t ht0 ht1
  refine le_trans ?_ (psiSmall_psiQ₀ t ht0 ht1)
  simp only [PsiParams.sigma, psiQ₁, psiQ₀]
  refine mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (Real.log t)]) (by norm_num))
    (by positivity)

/-- the pointwise real inequality behind the Hölder step -/
lemma pt_bound {R L ℓ h M X O ξ ρ : ℝ} (hR : 0 ≤ R) (hL : 0 < L) (hℓ : 0 < ℓ) (hh : 0 < h)
    (hρ : 1 < ρ)
    (hRL : R * L ≤ 4 * h * Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O)) :
    R ^ ρ ≤ (4 * h / ℓ) ^ ρ * (Real.exp (ρ ^ 2 * ξ * M) ^ (1 / ρ) *
      Real.exp (6 * ρ * ξ / (1 - 1 / ρ) * X) ^ ((1 - 1 / ρ) / 3) *
      Real.exp (18 * ρ * ξ / (1 - 1 / ρ) * O) ^ ((1 - 1 / ρ) / 3) *
      ((ℓ / L) ^ (3 * ρ / (1 - 1 / ρ))) ^ ((1 - 1 / ρ) / 3)) := by
  have hρ0 : 0 < ρ := by linarith
  have hu : 0 < 1 - 1 / ρ := by
    have : 1 / ρ < 1 := by rw [div_lt_one hρ0]; exact hρ
    linarith
  have hu' : (1 - 1 / ρ) ≠ 0 := hu.ne'
  have hρ1 : ρ - 1 ≠ 0 := by linarith
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul, ← Real.rpow_mul (div_pos hℓ hL).le]
  have e1 : ρ ^ 2 * ξ * M * (1 / ρ) = ξ * M * ρ := by field_simp
  have e2 : 6 * ρ * ξ / (1 - 1 / ρ) * X * ((1 - 1 / ρ) / 3) = 2 * ξ * X * ρ := by
    field_simp; ring
  have e3 : 18 * ρ * ξ / (1 - 1 / ρ) * O * ((1 - 1 / ρ) / 3) = 6 * ξ * O * ρ := by
    field_simp; ring
  have e4 : 3 * ρ / (1 - 1 / ρ) * ((1 - 1 / ρ) / 3) = ρ := by
    field_simp
  rw [e1, e2, e3, e4, Real.exp_mul (ξ * M) ρ, Real.exp_mul (2 * ξ * X) ρ,
    Real.exp_mul (6 * ξ * O) ρ,
    ← Real.mul_rpow (Real.exp_pos _).le (Real.exp_pos _).le,
    ← Real.mul_rpow (by positivity) (Real.exp_pos _).le,
    ← Real.mul_rpow (by positivity) (div_pos hℓ hL).le,
    ← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow hR ?_ hρ0.le
  have : R ≤ 4 * h * Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O) / L := by
    rw [le_div_iff₀ hL]; exact hRL
  refine this.trans (le_of_eq ?_)
  field_simp

/-- Step 5 (l. 1012–1016): the real asymptotics -/
lemma final_real_p21 {ρ u ξ q a K₁ cO KO AX AL ℓ A0 B1 B2 : ℝ} {K : ℕ}
    (hρ : 1 < ρ) (hu : 0 < u) (haρ : ρ ^ 2 * ξ = a) (hℓ : 0 < ℓ)
    (hℓK : (2 : ℝ) ^ (-((K : ℝ) * (1 - ξ * q + ξ * (q - 2) / 2))) ≤ ℓ) (hK1 : (1 : ℝ) ≤ K)
    (hA0 : A0 = ρ * Real.log 4 + u / 3 * (AX + Real.log 25 + AL))
    (hB1 : B1 = |Real.log 4 * K₁ / ρ| + u / 3 * |cO|) (hB2 : B2 = u / 3 * |KO|)
    (hasy : A0 + (0 : ℕ) * Real.log (K + 1) + B1 * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) +
      B2 * (K : ℝ) ^ (2 * (1 / 8 : ℝ)) + 0 * (K : ℝ) ^ ((2 : ℝ) / 3) ≤
        ρ * (ξ * (q - 2) / 2 * Real.log 2) / 2 * K) :
    ((4 * (2 : ℝ)⁻¹ ^ K / ℓ) ^ ρ * ((4 : ℝ) ^ (a * K + K₁ * √(K : ℝ))) ^ (1 / ρ) *
      Real.exp AX ^ (u / 3) * (25 * Real.exp (cO * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) +
        KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)))) ^ (u / 3) * Real.exp AL ^ (u / 3)) ^ (1 / ρ) ≤
      Real.exp (-(ξ * (q - 2) / 2 * Real.log 2 / 2 * K)) := by
  have hρ0 : 0 < ρ := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  set L2 := Real.log 2 with hL2
  have hL20 : 0 < L2 := Real.log_pos (by norm_num)
  have hL4 : Real.log 4 = 2 * L2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  set E := Real.exp (cO * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) + KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)))
  set x := a * K + K₁ * √(K : ℝ)
  have h4h : 0 < 4 * (2 : ℝ)⁻¹ ^ K / ℓ := by positivity
  have hB : 0 < (4 * (2 : ℝ)⁻¹ ^ K / ℓ) ^ ρ * ((4 : ℝ) ^ x) ^ (1 / ρ) * Real.exp AX ^ (u / 3) *
      (25 * E) ^ (u / 3) * Real.exp AL ^ (u / 3) := by positivity
  rw [Real.rpow_def_of_pos hB, Real.exp_le_exp]
  have hl1 : Real.log (4 * (2 : ℝ)⁻¹ ^ K / ℓ) ≤ 2 * L2 - K * L2 +
      K * (1 - ξ * q + ξ * (q - 2) / 2) * L2 := by
    rw [Real.log_div (by positivity) hℓ.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_inv, hL4]
    have := Real.log_le_log (by positivity) hℓK
    rw [Real.log_rpow (by norm_num)] at this
    push_cast; nlinarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow h4h, Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_mul (by norm_num) (Real.exp_pos _).ne', hL4]
  simp only [Real.log_exp]
  have hs : √(K : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  have hp1 : 0 ≤ (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) := by positivity
  have hp2 : 0 ≤ (K : ℝ) ^ (2 * (1 / 8 : ℝ)) := by positivity
  have hsq : 0 ≤ √(K : ℝ) := Real.sqrt_nonneg _
  have t1 : 2 * L2 * K₁ / ρ * √(K : ℝ) ≤ |Real.log 4 * K₁ / ρ| * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) := by
    rw [hL4]
    calc 2 * L2 * K₁ / ρ * √(K : ℝ) ≤ |2 * L2 * K₁ / ρ| * √(K : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hsq
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  have t2 : cO * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) ≤ |cO| * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hp1
  have t3 : KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)) ≤ |KO| * (K : ℝ) ^ (2 * (1 / 8 : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hp2
  have ex : 1 / ρ * (x * (2 * L2)) = 2 * ρ * ξ * K * L2 + 2 * L2 * K₁ / ρ * √(K : ℝ) := by
    simp only [x]; rw [← haρ]; field_simp
  have key : ρ * Real.log (4 * (2 : ℝ)⁻¹ ^ K / ℓ) ≤
      ρ * (2 * L2 - K * L2 + K * (1 - ξ * q + ξ * (q - 2) / 2) * L2) :=
    mul_le_mul_of_nonneg_left hl1 hρ0.le
  rw [hA0, hB1, hB2] at hasy
  have hu3 : 0 ≤ u / 3 := by positivity
  have t4 := mul_le_mul_of_nonneg_left t2 hu3
  have t5 := mul_le_mul_of_nonneg_left t3 hu3
  rw [ex, mul_one_div, div_le_iff₀ hρ0]
  simp only [Nat.cast_zero, zero_mul, add_zero] at hasy
  nlinarith [key, hasy, t1, t4, t5]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the `Obig` moment: `E e^{b O} ≤ 25 e^{c K^{5/8} + C K^{1/4}}` (from (2.17), DDDF l. 1001) -/
lemma obig_moment {b cO KO : ℝ} (hb : 0 < b)
    (hO : ∀ (n : ℕ) (Y : ℂ → Ω → ℝ),
      (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
      (∀ ω, ContDiff ℝ 1 fun x => Y x ω) → ∀ c₁ : ℂ,
      AEMeasurable (fun ω => ((2 : ℝ) ^ n)⁻¹ *
        ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖) P ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (b * (n : ℝ) ^ (1 / 8 : ℝ) * (((2 : ℝ) ^ n)⁻¹ *
        ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖))) ∂P ≤
        ENNReal.ofReal (Real.exp (cO * (n : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) +
          KO * (n : ℝ) ^ (2 * (1 / 8 : ℝ)))))
    {K : ℕ} (hK : 1 ≤ K) (Y : ℂ → Ω → ℝ)
    (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x)
    (hYc : ∀ ω, ContDiff ℝ 1 fun x => Y x ω) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (b * Obig K Y ω)) ∂P ≤
      ENNReal.ofReal (25 * Real.exp (cO * (K : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) +
        KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)))) := by
  set E := Real.exp (cO * (K : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) + KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)))
  set Oc : ℂ → Ω → ℝ := fun c₁ ω => ((2 : ℝ) ^ K)⁻¹ *
    ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖ with hOc
  have hKe : (1 : ℝ) ≤ (K : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hK) (by norm_num)
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (b * Obig K Y ω)) ≤
      ∑ c₁ ∈ offs, ENNReal.ofReal (Real.exp (b * (K : ℝ) ^ (1 / 8 : ℝ) * Oc c₁ ω)) := by
    intro ω
    obtain ⟨c₁, hc₁, he⟩ := Finset.exists_mem_eq_sup' offs_nonempty (fun c₁ => Oc c₁ ω)
    have e : Obig K Y ω = Oc c₁ ω := he
    have hO0 : 0 ≤ Oc c₁ ω := mul_nonneg (by positivity)
      (Real.iSup_nonneg fun _ => norm_nonneg _)
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) (Finset.single_le_sum
      (f := fun c₁ => ENNReal.ofReal (Real.exp (b * (K : ℝ) ^ (1 / 8 : ℝ) * Oc c₁ ω)))
      (fun _ _ => zero_le) hc₁)
    rw [e]
    have := mul_le_mul_of_nonneg_right hKe (mul_nonneg hb.le hO0)
    nlinarith
  calc _ ≤ ∫⁻ ω, ∑ c₁ ∈ offs, ENNReal.ofReal (Real.exp (b * (K : ℝ) ^ (1 / 8 : ℝ) *
        Oc c₁ ω)) ∂P := lintegral_mono hpt
    _ = ∑ c₁ ∈ offs, ∫⁻ ω, ENNReal.ofReal (Real.exp (b * (K : ℝ) ^ (1 / 8 : ℝ) *
        Oc c₁ ω)) ∂P := lintegral_finsetSum' _ fun c₁ _ =>
          (Real.measurable_exp.comp_aemeasurable
            ((hO K Y hY hYc c₁).1.const_mul _)).ennreal_ofReal
    _ ≤ ∑ c₁ ∈ offs, ENNReal.ofReal E := Finset.sum_le_sum fun c₁ _ => (hO K Y hY hYc c₁).2
    _ = (offs.card : ℝ≥0∞) * ENNReal.ofReal E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 25 * ENNReal.ofReal E := by gcongr; exact_mod_cast card_offs_le
    _ = ENNReal.ofReal (25 * E) := by rw [ENNReal.ofReal_mul (by norm_num)]; simp

/-- **DDDF Proposition 21** (`Prop:CondSatisfied`, `tightness.tex` l. 972–1018) for the
parameters `psiQ₁` of `ψ`, given (5.54). -/
theorem s6_conditionT_psiQ₁ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : IsWhiteNoise P W)
    (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) :
    ConditionT (xiGamma γ) psiQ₁ W P := by
  have := hW.isProbabilityMeasure
  set ξ := xiGamma γ with hξdef
  set q := LQGMetric.Q γ with hqdef
  have hξ0 : 0 < ξ := DG.xiGamma_pos hγ
  have hξ2 : ξ < 2 := by
    have hd := DG.one_le_dGamma DG.chiLeTwo hγ hγ2
    have : ξ ≤ γ := div_le_self hγ.le hd
    linarith
  have hq : 2 < q := by
    have e : q - 2 = (γ - 2) ^ 2 / (2 * γ) := by
      rw [hqdef, LQGMetric.Q]; field_simp; ring
    have : 0 < (γ - 2) ^ 2 / (2 * γ) := div_pos (by nlinarith) (by positivity)
    linarith
  set a : ℝ := (ξ + 2) / 2 with ha
  have ha0 : 0 < a := by positivity
  have ha2 : a < 2 := by linarith
  set ρ : ℝ := Real.sqrt (a / ξ) with hρdef
  have hρ2 : ρ ^ 2 = a / ξ := Real.sq_sqrt (by positivity)
  have hρ1 : 1 < ρ := by
    rw [hρdef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one (by rw [lt_div_iff₀ hξ0]; linarith)
  have hρ0 : 0 < ρ := by linarith
  have haρ : ρ ^ 2 * ξ = a := by rw [hρ2]; field_simp
  set u : ℝ := 1 - 1 / ρ with hu
  have hu0 : 0 < u := by
    have : 1 / ρ < 1 := by rw [div_lt_one hρ0]; exact hρ1
    linarith
  -- the constants
  obtain ⟨K₁, hK₁⟩ := prop2_expMoment_int ha0 ha2
  obtain ⟨hXm, MX, hMX⟩ := expMoment_XAB_shift hW psiQ₁ cBig 5 5 (l := 6 * ρ * ξ / u)
    (by positivity)
  obtain ⟨cO, KO, hO⟩ := prop3_expMoment_shift (by norm_num : (0 : ℝ) < 1 / 8)
    (a := 18 * ρ * ξ / u) (by positivity)
  obtain ⟨p₀, hp₀, hinv⟩ := invMoment_L11 (P := P) hW hξ0
  set p : ℝ := min p₀ (1 / 2)
  have hp : 0 < p := lt_min hp₀ (by norm_num)
  obtain ⟨ML, hML⟩ := hinv p hp (min_le_left _ _) (3 * ρ / u) (by positivity)
  obtain ⟨K₄, hK₄⟩ := h554 p hp (min_le_right _ _) (ξ * (q - 2) / 2) (by
    have : 0 < q - 2 := by linarith
    positivity)
  set AX : ℝ := Real.log (max MX 1)
  set AL : ℝ := Real.log (max ML 1)
  set κ : ℝ := ξ * (q - 2) / 2 * Real.log 2 with hκ
  have hκ0 : 0 < κ := by
    have : 0 < q - 2 := by linarith
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  set A0 : ℝ := ρ * Real.log 4 + u / 3 * (AX + Real.log 25 + AL)
  set B1 : ℝ := |Real.log 4 * K₁ / ρ| + u / 3 * |cO|
  set B2 : ℝ := u / 3 * |KO|
  obtain ⟨K₃, hK₃⟩ := asymp (c := ρ * κ) (ε := 1 / 8) (by positivity) (by norm_num) (by norm_num)
    A0 B1 B2 0 0 (by positivity) (by positivity) le_rfl
  refine ⟨ρ, hρ1, κ / 2, by positivity, max (max K₃ K₄) 2, fun η hη => ?_⟩
  obtain ⟨Γ, hΓ⟩ := exists_nearGeodSel hW psiQ₁ ξ hη
  refine ⟨Γ, hΓ, fun K hK n hn => ?_⟩
  have hK3 : K₃ ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hK4 : K₄ ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hK2 : 2 ≤ K := (le_max_right _ _).trans hK
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  obtain ⟨Y, -, hY, -, hYc, -⟩ := exists_C1_modification_phi hW (a := ((2 : ℝ) ^ K)⁻¹) (b := 1)
    (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 K x ω := by
    refine ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ K)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  set ℓ := ellN ξ W P K (ENNReal.ofReal p)
  obtain ⟨hℓ, hMLK⟩ := hML K
  have hℓK := hK₄ K hK4
  set h := (2 : ℝ)⁻¹ ^ K
  set F0 : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (a * ⨆ z : ferniqueBox 0 1, |Y z ω|))
  set F1 : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (6 * ρ * ξ / u * Xbig psiQ₁ W P ω))
  set F2 : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (18 * ρ * ξ / u * Obig K Y ω))
  set F3 : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal ((ℓ / lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω) ^ (3 * ρ / u))
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (condTRatio ξ K (fun x => psiMN psiQ₁ W P 0 K x ω)
      (Γ n ω) ^ ρ) ≤ ENNReal.ofReal ((4 * h / ℓ) ^ ρ) *
        (F0 ω ^ (1 / ρ) * F1 ω ^ (u / 3) * F2 ω ^ (u / 3) * F3 ω ^ (u / 3)) := by
    filter_upwards [hYeq, ae_XAB_shift_ne_top hW psiQ₁ cBig 5 5] with ω hω hfin
    have hRL := ratio_pathwise psiQ₁ hξ0 hK2 (hYc ω) hω hfin (hΓ.adm n ω)
    have hL0 : 0 < lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω := lenObs_pos hφK.cont _
      (by norm_num [rectAB]) (by norm_num [rectAB]) (by simp [rectAB, MarkedRect.crossWidth]) ω
    have hb := pt_bound (condTRatio_nonneg _ _ _ _) hL0 hℓ (h_pos' K) hρ1 hRL
    rw [haρ] at hb
    have hq0 : 0 ≤ (ℓ / lenObs ξ (phiMN W P 0 K) (rectAB 1 1) ω) ^ (3 * ρ / u) :=
      Real.rpow_nonneg (div_nonneg hℓ.le hL0.le) _
    simp only [F0, F1, F2, F3]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
      ENNReal.ofReal_rpow_of_nonneg hq0 (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hb
  -- measurability
  have hF0m : AEMeasurable F0 P :=
    ((aemeasurable_sup_abs hW (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
      hY fun ω => (hYc ω).continuous).const_mul a).exp.ennreal_ofReal
  have hF1m : AEMeasurable F1 P := (hXm.const_mul _).exp.ennreal_ofReal
  have hF2m : AEMeasurable F2 P :=
    ((aemeasurable_sup'_fun offs_nonempty fun c₁ _ => (hO hW K Y hY hYc c₁).1).const_mul
      _).exp.ennreal_ofReal
  have hF3m : AEMeasurable F3 P :=
    ((measurable_const.div (measurable_lenObs hφK.cont hφK.meas _)).pow_const
      _).ennreal_ofReal.aemeasurable
  -- Hölder
  have hH : ∫⁻ ω, F0 ω ^ (1 / ρ) * F1 ω ^ (u / 3) * F2 ω ^ (u / 3) * F3 ω ^ (u / 3) ∂P ≤
      (∫⁻ ω, F0 ω ∂P) ^ (1 / ρ) * (∫⁻ ω, F1 ω ∂P) ^ (u / 3) * (∫⁻ ω, F2 ω ∂P) ^ (u / 3) *
        (∫⁻ ω, F3 ω ∂P) ^ (u / 3) := by
    have h := ENNReal.lintegral_prod_norm_pow_le (μ := P) Finset.univ
      (f := ![F0, F1, F2, F3]) (fun i _ => by
        fin_cases i
        · exact hF0m
        · exact hF1m
        · exact hF2m
        · exact hF3m) (p := ![1 / ρ, u / 3, u / 3, u / 3])
      (by simp only [Fin.sum_univ_four, Matrix.cons_val]; rw [hu]; ring)
      (fun i _ => by fin_cases i <;> simp <;> positivity)
    simpa [Fin.prod_univ_four] using h
  -- the moments
  have m0 : ∫⁻ ω, F0 ω ∂P ≤ ENNReal.ofReal ((4 : ℝ) ^ (a * K + K₁ * √(K : ℝ))) := by
    obtain ⟨hint, hle⟩ := hK₁ hW K Y hY fun ω => (hYc ω).continuous
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hle
  have m1 : ∫⁻ ω, F1 ω ∂P ≤ ENNReal.ofReal (Real.exp AX) :=
    hMX.trans (ENNReal.ofReal_le_ofReal (by
      rw [Real.exp_log (by positivity)]; exact le_max_left _ _))
  have m2 := obig_moment (b := 18 * ρ * ξ / u) (cO := cO) (KO := KO) (by positivity)
    (fun n Y hY hYc c₁ => hO hW n Y hY hYc c₁) (by omega : 1 ≤ K) Y hY hYc
  have m3 : ∫⁻ ω, F3 ω ∂P ≤ ENNReal.ofReal (Real.exp AL) :=
    hMLK.trans (ENNReal.ofReal_le_ofReal (by
      rw [Real.exp_log (by positivity)]; exact le_max_left _ _))
  have hfinal := final_real_p21 (K := K) (K₁ := K₁) (cO := cO) (KO := KO) (AX := AX) (AL := AL)
    hρ1 hu0 haρ hℓ hℓK hK1r rfl rfl rfl (hK₃ K hK3)
  -- assembling
  have hI : ∫⁻ ω, ENNReal.ofReal (condTRatio ξ K (fun x => psiMN psiQ₁ W P 0 K x ω)
      (Γ n ω) ^ ρ) ∂P ≤ ENNReal.ofReal ((4 * h / ℓ) ^ ρ *
        ((4 : ℝ) ^ (a * K + K₁ * √(K : ℝ))) ^ (1 / ρ) * Real.exp AX ^ (u / 3) *
        (25 * Real.exp (cO * (K : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) + KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ))))
          ^ (u / 3) * Real.exp AL ^ (u / 3)) := by
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl hH).trans ?_
    have e1 := ENNReal.rpow_le_rpow m0 (by positivity : (0 : ℝ) ≤ 1 / ρ)
    have e2 := ENNReal.rpow_le_rpow m1 (by positivity : (0 : ℝ) ≤ u / 3)
    have e3 := ENNReal.rpow_le_rpow m2 (by positivity : (0 : ℝ) ≤ u / 3)
    have e4 := ENNReal.rpow_le_rpow m3 (by positivity : (0 : ℝ) ≤ u / 3)
    refine (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' (mul_le_mul' e1 e2) e3) e4)).trans
      (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  refine (ENNReal.rpow_le_rpow hI (by positivity)).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (hfinal.trans (le_of_eq ?_))
  congr 1

end S6

end DDDF
end LQGMetric
