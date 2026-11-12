/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.FieldMax at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (SupTail). -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGDimension.Gaussian.Concentration
import LatticeProb.Bonanno.LQGDimension.Blueprint.Gaussian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Covariance
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
DDDF (arXiv:1904.08021, `tightness.tex` l. 299–305), (2.10): for `α > 0`, `n ≥ 0`,
`P(max_{[0,1]²} |φ_{0,n}| ≥ α(n + C√n)) ≤ C 4^n e^{−α² n/log 4}`. DDDF give no proof ("corresponds
to Lemma 10.1 [...] in [DF18]"); we follow DF (arXiv:1809.02607) Lemma 10.1, l. 1823–1858:
union bound and Gaussian tails on the grid `2^{-n}ℤ² ∩ [0,1)²`, then
`sup_{[0,1]²} |φ| ≤ max_grid |φ| + 2 · 2^{-n} sup_{[0,1]²} |∇φ|` (mean value theorem) and the
gradient tail (2.16) (`prop3_tail`). Constants differ from DF: here `Var φ_{0,n}(x) = n log 2`
(`variance_phi_delta`; DF: `(n+1) log 2`), and the grid has the `4^n` lower-left corners of the
dyadic squares, at distance `≤ 2 · 2^{-n}` from every point of their square.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped RealInnerProductSpace

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Two-sided Gaussian tail: `P(|U| ≥ y) ≤ 2 e^{−y²/(2v)}` for `U ~ N(0, v)`, `v > 0`, `y ≥ 0`
(Chernoff, mathlib `measure_ge_le_exp_mul_mgf`). -/
lemma tail_abs_of_hasLaw [IsProbabilityMeasure P] {U : Ω → ℝ} {v : NNReal} (hv : 0 < (v : ℝ))
    (hU : HasLaw U (gaussianReal 0 v) P) {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | y ≤ |U ω|} ≤ 2 * Real.exp (-y ^ 2 / (2 * v)) := by
  have hint : ∀ t, Integrable (fun ω => Real.exp (t * U ω)) P := fun t => by
    have := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hU.map_eq] at this
    exact (integrable_map_measure (by fun_prop) hU.aemeasurable).1 this
  have hmgf : ∀ t, mgf U P t = Real.exp (v * t ^ 2 / 2) := fun t => by
    rw [← mgf_id_map hU.aemeasurable, hU.map_eq, mgf_id_gaussianReal]; ring_nf
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := U) y (t := y / v) (by positivity)
    (hint _)
  have h2 := measure_le_le_exp_mul_mgf (μ := P) (X := U) (-y) (t := -(y / v))
    (by have : 0 ≤ y / v := by positivity
        linarith) (hint _)
  rw [hmgf] at h1 h2
  have e1 : Real.exp (-(y / v) * y) * Real.exp (v * (y / v) ^ 2 / 2) =
      Real.exp (-y ^ 2 / (2 * v)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have e2 : Real.exp (-(-(y / v)) * -y) * Real.exp (v * (-(y / v)) ^ 2 / 2) =
      Real.exp (-y ^ 2 / (2 * v)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [e1] at h1
  rw [e2] at h2
  have hsub : {ω | y ≤ |U ω|} ⊆ {ω | y ≤ U ω} ∪ {ω | U ω ≤ -y} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right; linarith
    · left; exact h
  calc P.real {ω | y ≤ |U ω|} ≤ P.real ({ω | y ≤ U ω} ∪ {ω | U ω ≤ -y}) := measureReal_mono hsub
    _ ≤ P.real {ω | y ≤ U ω} + P.real {ω | U ω ≤ -y} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-y ^ 2 / (2 * v)) := by linarith

variable {W : WNSpace → Ω → ℝ}

end DDDF
end LQGMetric
