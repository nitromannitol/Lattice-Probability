/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdentKer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdentTilde
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
# White-noise kernels of measures and their fine/coarse splitting (P2-GMCID, D67)

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

lemma wndKernel_split (A : Set ℂ) {c : ℝ} (hc : 0 < c) (y : ℂ) (p : ℝ × ℂ) :
    wndKernel A (Ioi 0) y p = wndKernel A (Ioc 0 c) y p + wndKernel A (Ioi c) y p := by
  unfold wndKernel
  by_cases h0 : 0 < p.1
  · by_cases h1 : p.1 ≤ c
    · have h2 : p.1 ∉ Ioi c := fun h => absurd h1 (not_le.2 h)
      rw [indicator_of_mem (mem_Ioi.2 h0), indicator_of_mem (mem_Ioc.2 ⟨h0, h1⟩),
        indicator_of_notMem h2, add_zero]
    · have h2 : p.1 ∉ Ioc 0 c := fun h => h1 h.2
      rw [indicator_of_mem (mem_Ioi.2 h0), indicator_of_notMem h2,
        indicator_of_mem (mem_Ioi.2 (not_le.1 h1)), zero_add]
  · have h2 : p.1 ∉ Ioc 0 c := fun h => h0 h.1
    have h3 : p.1 ∉ Ioi c := fun h => h0 (hc.trans h)
    have h4 : p.1 ∉ Ioi (0 : ℝ) := fun h => h0 (mem_Ioi.1 h)
    rw [indicator_of_notMem h4, indicator_of_notMem h2, indicator_of_notMem h3, add_zero]

/-- `K^{(0,∞)}_μ = K^{(0,c]}_μ + K^{(c,∞)}_μ` -/
lemma measKer_split {A : Set ℂ} (hA : IsOpen A) {c : ℝ} (hc : 0 < c) (μ : Measure ℂ)
    [IsFiniteMeasure μ] :
    measKer A (Ioi 0) μ = measKer A (Ioc 0 c) μ + measKer A (Ioi c) μ := by
  funext p
  simp only [measKer, Pi.add_apply]
  rw [← integral_add (integrable_wndKernel_param hA Ioc_subset_Ioi_self μ p)
    (integrable_wndKernel_param hA (Ioi_subset_Ioi hc.le) μ p)]
  exact integral_congr_ae (Eventually.of_forall fun y => wndKernel_split A hc y p)

lemma measKerL2_split {A : Set ℂ} (hA : IsOpen A) {c : ℝ} (hc : 0 < c) (μ : Measure ℂ)
    [IsFiniteMeasure μ] (h₁ : MemLp (measKer A (Ioc 0 c) μ) 2 volume)
    (h₂ : MemLp (measKer A (Ioi c) μ) 2 volume) :
    measKerL2 A (Ioi 0) μ = measKerL2 A (Ioc 0 c) μ + measKerL2 A (Ioi c) μ := by
  have hs := measKer_split hA hc μ
  have h0 : MemLp (measKer A (Ioi 0) μ) 2 volume := hs ▸ h₁.add h₂
  rw [measKerL2, measKerL2, measKerL2, dite_eq_left_of_eq_true (eq_true h0), dite_eq_left_of_eq_true (eq_true h₁),
    dite_eq_left_of_eq_true (eq_true h₂), ← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun p => by rw [hs])

/-- `K^I_μ` is supported in `I × ℂ`. -/
lemma supportedIn_measKerL2 (A : Set ℂ) {I : Set ℝ} (hI : MeasurableSet I) (μ : Measure ℂ) :
    SupportedIn (I ×ˢ univ) (measKerL2 A I μ) := by
  unfold measKerL2
  split_ifs with h
  · refine supportedIn_toLp (hI.prod MeasurableSet.univ) h fun p hp => ?_
    have : p.1 ∉ I := fun h1 => hp ⟨h1, trivial⟩
    simp [measKer, wndKernel, this]
  · unfold SupportedIn
    exact ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 volume)

/-- the fine scales `(0, 4^{-n}]` lie outside the coarse set -/
lemma fine_subset_compl_coarseSet (n : ℕ) :
    Ioc 0 (((2 : ℝ)⁻¹ ^ n) ^ 2) ×ˢ (univ : Set ℂ) ⊆ (coarseSet n)ᶜ := by
  rintro p ⟨hp, -⟩ ⟨hq, -⟩
  exact absurd hp.2 (not_le.2 (mem_Ioi.1 hq))

end GMCIdent
end LQGMetric
