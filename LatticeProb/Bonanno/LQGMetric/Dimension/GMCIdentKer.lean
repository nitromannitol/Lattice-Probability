/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentKer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoise
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqReg
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Bridge
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2Box
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailField
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueDZZ

/-!
For a finite measure `μ` (in the application a circle `∂B(z, 2^{-k})`), DZZ's white-noise
representation of the field average `(h, μ)` (`LBM_LGDarXiv.tex` l. 430–433, the decomposition
`h = lim_δ h̃_δ`) uses the kernel `K^I_μ(s, w) = ∫ 1_I(s) p_𝕍(s/2; y, w) μ(dy)` (`measKer`):
`(h, μ) = √π W(K^{(0,∞)}_μ)`. Here:

* `measKer`, `measKerL2` (its `L²` class, junk `0` if not square integrable);
* `integrable_wndKernel_param` : `y ↦ 1_I(s) p_A(s/2; y, w)` is `μ`-integrable (`p_A ≤ 1/(πs)`);
* `measKer_split` / `measKerL2_split` : `K^{(0,∞)} = K^{(0,c]} + K^{(c,∞)}`;
* `supportedIn_measKerL2` : `K^I_μ` is supported in `I × ℂ`.

With `c = 4^{-n}` the two pieces are supported in the fine and the coarse scales, so `W(K^{(0,c]})`
is independent of `𝓖_n` and `W(K^{(c,∞)})` is `𝓖_n`-measurable (`GMCIdentWN.condExp_exp_wn`):
the decomposition "`h = h^n + X` with `X` independent of `h^n`" of Berestycki
(arXiv:1506.09113, §4, l. 685).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace LQGMetric
namespace GMCIdent

open WhiteNoise DZZ KilledHeat

/-- `K^I_μ(s, w) = ∫ 1_I(s) p_A(s/2; y, w) μ(dy)` -/
def measKer (A : Set ℂ) (I : Set ℝ) (μ : Measure ℂ) (p : ℝ × ℂ) : ℝ :=
  ∫ y, wndKernel A I y p ∂μ

open Classical in
/-- the `L²` class of `measKer` (junk `0` if it is not square integrable) -/
def measKerL2 (A : Set ℂ) (I : Set ℝ) (μ : Measure ℂ) : WNSpace :=
  if h : MemLp (measKer A I μ) 2 volume then h.toLp _ else 0

lemma wndKernel_le (A : Set ℂ) (I : Set ℝ) (y : ℂ) (p : ℝ × ℂ) (hp : 0 < p.1) :
    wndKernel A I y p ≤ (Real.pi * p.1)⁻¹ := by
  unfold wndKernel
  by_cases h : p.1 ∈ I
  · rw [indicator_of_mem h]
    refine (killedHeat_le_heatKernel A _ y p.2).trans ((heatKernel_le_inv _ (by positivity) _ _).trans
      (le_of_eq ?_))
    rw [Real.coe_toNNReal _ (by positivity)]; ring
  · rw [indicator_of_notMem h]; positivity

lemma integrable_wndKernel_param {A : Set ℂ} (hA : IsOpen A) {I : Set ℝ} (hI0 : I ⊆ Ioi 0) (μ : Measure ℂ) [IsFiniteMeasure μ] (p : ℝ × ℂ) :
    Integrable (fun y => wndKernel A I y p) μ := by
  by_cases hp : p.1 ∈ I
  · refine Integrable.of_bound (C := (Real.pi * p.1)⁻¹) ?_ (Eventually.of_forall fun y => ?_)
    · have e : (fun y => wndKernel A I y p) =
          fun y => killedHeat A (p.1 / 2).toNNReal y p.2 := by
        funext y; simp [wndKernel, hp]
      rw [e]
      exact ((measurable_killedHeat hA).comp
        (measurable_const.prodMk (measurable_id.prodMk measurable_const))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (wndKernel_nonneg _ _ _ _)]
      exact wndKernel_le A I y p (hI0 hp)
  · have : (fun y => wndKernel A I y p) = fun _ => 0 := by
      funext y; simp [wndKernel, hp]
    rw [this]; exact integrable_zero _ _ _

end GMCIdent
end LQGMetric
