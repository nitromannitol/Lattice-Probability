/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinSup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffZBApx
import LatticeProb.Bonanno.LQGMetric.LFPP.LocalizedCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Zero-boundary analogue of DFGPS Lemma 2.1, uniformly in `x` (T:883–885): deterministic part

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:883–885): Lemma 2.1 "remains true"
for the zero-boundary GFF `h̊` on `(-1,2)²`. For each `x ∈ [0,1]²`,
`Y_{ε²}(x) − ĥ̊*_ε(x) = Xh(T_x)` with the tail density `T_x = p_{ε²/2}(x,·)1_V − ψ_ε(x−·)p_{ε²/2}(x,·)`
(`zbLoc_ae_tail`). This file proves the deterministic estimates on `T_x` feeding the Gaussian sup
bound (`L2_8FinSupMain.lean`):

* `abs_zbTail_le`: `|T_x| ≤ C_t(ε) = 2 e^{−1/(8ε)} (2π ε²)⁻¹`;
* `integral_abs_zbTail_sub_le`: `∫ |T_x − T_{x'}| ≤ (2K_h(ε) + L₀ · 2/√ε) ‖x − x'‖`, with `K_h` the
  `L¹`-Lipschitz constant of the heat kernel (`integral_abs_heat_sub_le`) and `L₀` the Lipschitz
  constant of mathlib's base bump (`exists_lipschitz_bumpBase`);
* `tendsto_inv_pow_mul_exp`: `ε^{−n} e^{−1/(8ε)} → 0` (from `x^n e^{−x} → 0`);
* `clampSq`: the 1-Lipschitz retraction of `ℂ` onto `[0,1]²`.

Own elementary estimates (the paper says "with the same proof"); the GFF proof (T:726–733) uses
the polar formula and Lemma 2.2, which we replace by the Gaussian sup bound of DZZ Lemma 2.3 +
Borell–TIS (`SupTail.tail_iSup_abs_box`), see `L2_8FinSupMain.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open LFPP HeatSq Blueprint

/-- clamp to `[0,1]` -/
def clampR (a : ℝ) : ℝ := max 0 (min 1 a)

lemma abs_clampR_sub_le (a b : ℝ) : |clampR a - clampR b| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  unfold clampR
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- the retraction of `ℂ` onto `[0,1]²` -/
def clampSq (z : ℂ) : ℂ := ⟨clampR z.re, clampR z.im⟩

lemma continuous_clampR : Continuous clampR :=
  continuous_const.max (continuous_const.min continuous_id)

lemma continuous_clampSq : Continuous clampSq := by
  have : clampSq = fun z => Complex.equivRealProdCLM.symm (clampR z.re, clampR z.im) := by
    funext z; rfl
  rw [this]
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_clampR.comp Complex.continuous_re).prodMk
      (continuous_clampR.comp Complex.continuous_im))

lemma clampSq_mem (z : ℂ) : clampSq z ∈ closedUnitSquare := by
  refine ⟨le_max_left _ _, ?_, le_max_left _ _, ?_⟩ <;>
    exact max_le zero_le_one (min_le_left _ _)

lemma clampSq_of_mem {z : ℂ} (hz : z ∈ closedUnitSquare) : clampSq z = z := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  apply Complex.ext
  · show max 0 (min 1 z.re) = z.re
    rw [min_eq_right h2, max_eq_right h1]
  · show max 0 (min 1 z.im) = z.im
    rw [min_eq_right h4, max_eq_right h3]

lemma norm_clampSq_sub_le (u v : ℂ) : ‖clampSq u - clampSq v‖ ≤ ‖u - v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  have hre : (clampSq u - clampSq v).re = clampR u.re - clampR v.re := rfl
  have him : (clampSq u - clampSq v).im = clampR u.im - clampR v.im := rfl
  rw [hre, him, Complex.sub_re, Complex.sub_im]
  have e1 := sq_le_sq.2 (abs_clampR_sub_le u.re v.re)
  have e2 := sq_le_sq.2 (abs_clampR_sub_le u.im v.im)
  nlinarith

/-- closed balls of radius `< 1` around points of `[0,1]²` lie in `(-1,2)²` -/
lemma closedBall_subset_sqOpen {x : ℂ} (hx : x ∈ closedUnitSquare) {r : ℝ} (hr : r < 1) :
    closedBall x r ⊆ sqOpen (-1) 3 := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hd : ‖z - x‖ ≤ r := by rw [← dist_eq_norm]; exact hz
  have a1 := (Complex.abs_re_le_norm (z - x)).trans hd
  have a2 := (Complex.abs_im_le_norm (z - x)).trans hd
  rw [Complex.sub_re, abs_le] at a1
  rw [Complex.sub_im, abs_le] at a2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [a1.1, a1.2, a2.1, a2.2]

/-- the base bump `φ = (ofInnerProductSpace ℂ).toFun 2` is Lipschitz -/
lemma exists_lipschitz_bumpBase :
    ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ y y' : ℂ, |(ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y -
      (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y'| ≤ L₀ * ‖y - y'‖ := by
  set φ : ℂ → ℝ := (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : ℂ => ((2 : ℝ), y) :=
    contDiff_const.prodMk contDiff_id
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ :=
    ((ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff hf
      fun _ => ⟨by norm_num, mem_univ _⟩).of_le le_rfl
  have hs := (ContDiffBumpBase.ofInnerProductSpace ℂ).support 2 (by norm_num)
  have hφs : HasCompactSupport φ := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2)
    fun y hy => Function.notMem_support.1 fun h' => by
      rw [hs] at h'; exact hy (ball_subset_closedBall h')
  obtain ⟨C, hC⟩ := hφ.lipschitzWith_of_hasCompactSupport hφs (by simp)
  refine ⟨C, C.2, fun y y' => ?_⟩
  rw [← Real.dist_eq, ← dist_eq_norm]
  exact hC.dist_le_mul y y'

lemma abs_locBump_sub_le {L₀ : ℝ} (hL₀ : 0 ≤ L₀) (hL : ∀ y y' : ℂ,
      |(ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y -
        (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y'| ≤ L₀ * ‖y - y'‖)
    {ε : ℝ} (hε : 0 < ε) (a b : ℂ) :
    |locBump ε hε a - locBump ε hε b| ≤ L₀ * (2 / Real.sqrt ε) * ‖a - b‖ := by
  have hs := Real.sqrt_pos.2 hε
  unfold locBump
  refine (hL _ _).trans (le_of_eq ?_)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

/-- `K_h(ε)`: the `L¹`-Lipschitz constant of `x ↦ p_{ε²/2}(x,·)1_{(-1,2)²}` -/
def kHeat (ε : ℝ) : ℝ := (16 * Real.pi * (ε ^ 2 / 2) ^ 2)⁻¹ + 3 ^ 2 / 2

lemma kHeat_nonneg (ε : ℝ) : 0 ≤ kHeat ε := by unfold kHeat; positivity

/-- `L¹`-Lipschitz bound for the localized densities, explicit in `ε` -/
lemma integral_abs_locTest_sub_le' {L₀ : ℝ} (hL₀ : 0 ≤ L₀) (hL : ∀ y y' : ℂ,
      |(ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y -
        (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y'| ≤ L₀ * ‖y - y'‖)
    {ε : ℝ} (hε : 0 < ε) (x x' : ℂ) (hx' : closedBall x' (Real.sqrt ε) ⊆ sqOpen (-1) 3) :
    ∫ w, |locTest ε hε x w - locTest ε hε x' w| ≤
      (L₀ * (2 / Real.sqrt ε) + kHeat ε) * ‖x - x'‖ := by
  set s : ℝ := ε ^ 2 / 2
  have hs : 0 < s := by positivity
  set V := sqOpen (-1) 3
  have hV := measurableSet_sqOpen (-1) 3
  set c := L₀ * (2 / Real.sqrt ε) * ‖x - x'‖
  have hpt : ∀ w, |locTest ε hε x w - locTest ε hε x' w| ≤
      c * heatKernel s x w + |V.indicator (fun w => heatKernel s x w) w -
        V.indicator (fun w => heatKernel s x' w) w| := by
    intro w
    rw [locTest_apply', locTest_apply']
    have hp := heatKernel_nonneg s hs.le x w
    have hb := abs_locBump_sub_le hL₀ hL hε (x - w) (x' - w)
    rw [show x - w - (x' - w) = x - x' by ring] at hb
    have hb0 := locBump_nonneg ε hε (x' - w)
    have hb1 := locBump_le_one ε hε (x' - w)
    have e : locBump ε hε (x - w) * heatKernel s x w - locBump ε hε (x' - w) * heatKernel s x' w
        = (locBump ε hε (x - w) - locBump ε hε (x' - w)) * heatKernel s x w +
          locBump ε hε (x' - w) * (heatKernel s x w - heatKernel s x' w) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_right hb hp
    · by_cases hw : w ∈ V
      · rw [indicator_of_mem hw, indicator_of_mem hw, abs_mul, abs_of_nonneg hb0]
        exact mul_le_of_le_one_left (abs_nonneg _) hb1
      · have hw' : w ∉ closedBall x' (Real.sqrt ε) := fun h => hw (hx' h)
        rw [locBump_comp_eq_zero ε hε x' hw', zero_mul, abs_zero]
        exact abs_nonneg _
  have hi1 : Integrable fun w => c * heatKernel s x w :=
    (integrable_heatKernel s hs x).const_mul c
  have hi2 : Integrable fun w => |V.indicator (fun w => heatKernel s x w) w -
      V.indicator (fun w => heatKernel s x' w) w| :=
    (((integrable_heatKernel s hs x).indicator hV).sub
      ((integrable_heatKernel s hs x').indicator hV)).abs
  calc ∫ w, |locTest ε hε x w - locTest ε hε x' w|
      ≤ ∫ w, (c * heatKernel s x w + |V.indicator (fun w => heatKernel s x w) w -
          V.indicator (fun w => heatKernel s x' w) w|) :=
        integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _) (hi1.add hi2)
          (ae_of_all _ hpt)
    _ = c + ∫ w, |V.indicator (fun w => heatKernel s x w) w -
          V.indicator (fun w => heatKernel s x' w) w| := by
        rw [integral_add hi1 hi2, integral_const_mul, integral_heatKernel _ hs, mul_one]
    _ ≤ c + ‖x - x'‖ * kHeat ε := by
        gcongr
        exact integral_abs_heat_sub_le (by norm_num) hs x x'
    _ = (L₀ * (2 / Real.sqrt ε) + kHeat ε) * ‖x - x'‖ := by ring

lemma zbTail_apply {ε : ℝ} (hε : 0 < ε) (x : ℂ)
    (hsupp : tsupport (locTest ε hε x : ℂ → ℝ) ⊆ (sqOpens (-1) 3 : Set ℂ)) (w : ℂ) :
    (zbTail hε x hsupp).1 w =
      (sqOpen (-1) 3).indicator (fun w => heatKernel (ε ^ 2 / 2) x w) w - locTest ε hε x w := by
  have h := heatBdd_val (U := ((sqOpens (-1) 3 : Opens ℂ) : Set ℂ)) (measurableSet_sqOpen (-1) 3)
    (s := ε ^ 2 / 2) (by positivity) x
  show (heatBdd (sqOpens (-1) 3) (ε ^ 2 / 2) x).1 w - locTest ε hε x w = _
  rw [h]
  rfl

/-- `C_t(ε)`: the uniform bound of the tail densities -/
def cTail (ε : ℝ) : ℝ := 2 * Real.exp (-(1 / (8 * ε))) * (2 * Real.pi * ε ^ 2)⁻¹

lemma cTail_nonneg (ε : ℝ) : 0 ≤ cTail ε := by unfold cTail; positivity

lemma abs_zbTail_le {ε : ℝ} (hε : 0 < ε) (x : ℂ)
    (hsupp : tsupport (locTest ε hε x : ℂ → ℝ) ⊆ (sqOpens (-1) 3 : Set ℂ)) (w : ℂ) :
    |(zbTail hε x hsupp).1 w| ≤ cTail ε := by
  rw [zbTail_apply]
  exact (abs_heat_sub_locTest_le hε x w hsupp).trans (mul_le_mul_of_nonneg_left
    (KilledHeat.heatKernel_le_inv _ (by positivity) x w) (by positivity))

/-- **`L¹` increments of the tail densities** -/
lemma integral_abs_zbTail_sub_le {L₀ : ℝ} (hL₀ : 0 ≤ L₀) (hL : ∀ y y' : ℂ,
      |(ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y -
        (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 y'| ≤ L₀ * ‖y - y'‖)
    {ε : ℝ} (hε : 0 < ε) (x x' : ℂ)
    (hs : tsupport (locTest ε hε x : ℂ → ℝ) ⊆ (sqOpens (-1) 3 : Set ℂ))
    (hs' : tsupport (locTest ε hε x' : ℂ → ℝ) ⊆ (sqOpens (-1) 3 : Set ℂ))
    (hx' : closedBall x' (Real.sqrt ε) ⊆ sqOpen (-1) 3) :
    ∫ w, |(zbTail hε x hs).1 w - (zbTail hε x' hs').1 w| ≤
      (2 * kHeat ε + L₀ * (2 / Real.sqrt ε)) * ‖x - x'‖ := by
  set s : ℝ := ε ^ 2 / 2
  have hs0 : 0 < s := by positivity
  have hV := measurableSet_sqOpen (-1) 3
  set H : ℂ → ℂ → ℝ := fun y w => (sqOpen (-1) 3).indicator (fun w => heatKernel s y w) w
  have hHi : ∀ y, Integrable (H y) := fun y => (integrable_heatKernel s hs0 y).indicator hV
  have hi1 : Integrable fun w => |H x w - H x' w| := ((hHi x).sub (hHi x')).abs
  have hi2 : Integrable fun w => |locTest ε hε x w - locTest ε hε x' w| :=
    ((integrable_locTest ε hε x).sub (integrable_locTest ε hε x')).abs
  have hpt : ∀ w, |(zbTail hε x hs).1 w - (zbTail hε x' hs').1 w| ≤
      |H x w - H x' w| + |locTest ε hε x w - locTest ε hε x' w| := by
    intro w
    rw [zbTail_apply, zbTail_apply]
    rw [show H x w - locTest ε hε x w - (H x' w - locTest ε hε x' w) =
      (H x w - H x' w) - (locTest ε hε x w - locTest ε hε x' w) by ring]
    exact abs_sub _ _
  calc ∫ w, |(zbTail hε x hs).1 w - (zbTail hε x' hs').1 w|
      ≤ ∫ w, (|H x w - H x' w| + |locTest ε hε x w - locTest ε hε x' w|) :=
        integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _) (hi1.add hi2)
          (ae_of_all _ hpt)
    _ = (∫ w, |H x w - H x' w|) + ∫ w, |locTest ε hε x w - locTest ε hε x' w| :=
        integral_add hi1 hi2
    _ ≤ ‖x - x'‖ * kHeat ε + (L₀ * (2 / Real.sqrt ε) + kHeat ε) * ‖x - x'‖ :=
        add_le_add (integral_abs_heat_sub_le (by norm_num) hs0 x x')
          (integral_abs_locTest_sub_le' hL₀ hL hε x x' hx')
    _ = (2 * kHeat ε + L₀ * (2 / Real.sqrt ε)) * ‖x - x'‖ := by ring

/-- `ε^{−n} e^{−1/(8ε)} → 0` as `ε → 0+` -/
lemma tendsto_inv_pow_mul_exp (n : ℕ) :
    Tendsto (fun ε : ℝ => ε⁻¹ ^ n * Real.exp (-(1 / (8 * ε)))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ => ε⁻¹ / 8) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.atTop_div_const (by norm_num)
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp h1).const_mul ((8 : ℝ) ^ n)
  rw [mul_zero] at h2
  refine h2.congr fun ε => ?_
  simp only [Function.comp_apply]
  have e : ε⁻¹ / 8 = 1 / (8 * ε) := by rw [one_div, mul_inv, div_eq_mul_inv, mul_comm]
  rw [e, div_pow, ← e]
  simp only [e]
  rw [one_pow, mul_pow, ← mul_assoc, one_div, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero n (by norm_num : (8 : ℝ) ≠ 0)), one_mul, inv_pow]

end LQGMetric.DFGPS
