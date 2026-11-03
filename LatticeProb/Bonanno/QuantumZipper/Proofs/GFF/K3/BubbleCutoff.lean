/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.BubbleCutoff at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.MixedPoincare
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# K3-BUB2: vertical Poincaré on a ball, and the logarithmic cutoff

This file contains the two analytic inputs of the "gate lemma" that replaces `C4` in the
K3 / Thm 1.1 addendum (blueprint `EXT_PP_BLUEPRINT.md` §B, BUB-2).

* `integral_sq_ball_le`: *vertical Poincaré on a ball*. If `f : ℂ → ℝ` is `C¹` with compact
  support and vanishes on the closed lower half-plane `{Im ≤ 0}`, then for every `p` and `R > 0`
  ```
  ∫_{B(p,R)} f² ≤ 2R (|Im p| + R) ∫_ℂ ‖∇f‖².
  ```
  Proof: for `z ∈ B(p,R)` integrate `∂_y f` along the vertical segment from the real axis
  (where `f = 0`) up to `z`; Cauchy–Schwarz in one dimension, then Tonelli along the vertical
  fibres, using that the vertical section of `B(p,R)` has length `2R` and lies in
  `[Im p - R, Im p + R]`, so `Im z ≤ |Im p| + R` there. Own elementary proof (the blueprint
  writes "S (~200)"; no published source is needed for this elementary estimate).

* `logCutoffConst`, `exists_logCutoff`: the *logarithmic cutoff*. For `0 < r` and `2r < R`
  there is a smooth `χ : ℂ → ℝ` with values in `[0,1]`, equal to `0` on `B(p, 2r)`, equal to `1`
  off `B(p, R)`, and with
  ```
  ‖∇χ x‖ ≤ logCutoffConst / (log (R / (2r)) * ‖x - p‖).
  ```
  The construction is `χ x = ψ (log ‖x - p‖)` with `ψ` an affine rescaling of
  `Real.smoothTransition` onto the window `[log (2r), log R]`; the rescaling divides the
  derivative by the window length, which produces the factor `log (R/(2r))`. The constant
  `logCutoffConst` bounds `|deriv Real.smoothTransition|` (see
  `bubbleCutoff_abs_deriv_smoothTransition_le`), which is estimated here by an elementary
  computation. Own elementary proof (blueprint EXT_PP §B, BUB-2).

Blueprint: EXT_PP §B, BUB-2. Namespace `QuantumZipper.K3`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace QuantumZipper.K3

/-! ## 1. Vertical Poincaré on a ball -/

/-- **Vertical Poincaré inequality on a ball.** A `C¹` function with compact support which
vanishes on the closed lower half-plane is controlled on any ball by the `L²` norm of its
gradient, with constant `2R (|Im p| + R)`. -/
theorem integral_sq_ball_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hf0 : ∀ z : ℂ, z.im ≤ 0 → f z = 0) (p : ℂ) {R : ℝ} (hR : 0 < R) :
    ∫ x in Metric.ball p R, f x ^ 2 ≤ 2 * R * (|p.im| + R) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ f := hf.differentiable hn
  have hcf : Continuous (fderiv ℝ f) := hf.continuous_fderiv hn
  set g : ℂ → ℝ := fun w => ‖fderiv ℝ f w‖ ^ 2 with hg
  have hgc : Continuous g := hcf.norm.pow 2
  have hgcs : HasCompactSupport g := by
    rw [hg]
    exact (hfc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => ‖L‖ ^ 2)
      (by rw [norm_zero]; norm_num)
  have hgint : Integrable g := hgc.integrable_of_hasCompactSupport hgcs
  have hgfin : ∫⁻ z, ENNReal.ofReal (g z) < ∞ := hgint.lintegral_lt_top
  set F : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (g w) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp hgc.measurable
  set G : ℝ → ℝ≥0∞ := fun x => ∫⁻ s, F ⟨x, s⟩ with hG
  have hFm' : Measurable fun q : ℝ × ℝ => F ⟨q.1, q.2⟩ :=
    hFm.comp (Complex.measurableEquivRealProd.symm.measurable)
  have hGm : Measurable G := hFm'.lintegral_prod_right'
  have hGint : ∫⁻ x, G x = ∫⁻ z, ENNReal.ofReal (g z) := by
    change ∫⁻ x, ∫⁻ s, F ⟨x, s⟩ = ∫⁻ z, F z
    rw [← lintegral_prod _ hFm'.aemeasurable, ← Measure.volume_eq_prod]
    exact (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding F
  -- 1-D bound along the upward vertical ray from the real axis to `z`
  have hpt : ∀ z : ℂ, ENNReal.ofReal (f z ^ 2) ≤ ENNReal.ofReal (max z.im 0) * G z.re := by
    intro z
    rcases lt_trichotomy z.im 0 with hz | hz | hz
    · simp [hf0 z hz.le, max_eq_right hz.le]
    · simp [hf0 z hz.le, max_eq_right hz.le]
    · have hzim : 0 < z.im := hz
      set γ : ℝ → ℂ := fun t => (z.re : ℂ) + (t : ℂ) * Complex.I with hγdef
      have hγc : Continuous γ :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have hγd : ∀ t, HasDerivAt γ (((1 : ℝ) : ℂ) * Complex.I) t := fun t =>
        ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).const_add (z.re : ℂ)
      have hγim : ∀ t, (γ t).im = t := fun t => by simp [hγdef]
      have hγre : ∀ t, (γ t).re = z.re := fun t => by simp [hγdef]
      have hγeq : ∀ t, γ t = ⟨z.re, t⟩ := fun t => Complex.ext (hγre t) (hγim t)
      have hγT : γ z.im = z := by rw [hγeq]
      have hγ0 : γ 0 = ⟨z.re, 0⟩ := by rw [hγeq]
      set φ' : ℝ → ℝ := fun t => fderiv ℝ f (γ t) (((1 : ℝ) : ℂ) * Complex.I) with hφ'
      have hφc : Continuous φ' := (hcf.comp hγc).clm_apply continuous_const
      have hderiv : ∀ t, HasDerivAt (fun t => f (γ t)) (φ' t) t := fun t =>
        (hdiff (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
      have hftc : ∫ t in (0:ℝ)..z.im, φ' t = f (γ z.im) - f (γ 0) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
          (hφc.intervalIntegrable _ _)
      have hfbot : f (γ 0) = 0 := by rw [hγ0]; exact hf0 _ (by simp)
      rw [hγT, hfbot, sub_zero] at hftc
      have hφle : ∀ t, φ' t ^ 2 ≤ g (γ t) := fun t => by
        have h1 : ‖φ' t‖ ≤ ‖fderiv ℝ f (γ t)‖ := by
          have h := (fderiv ℝ f (γ t)).le_opNorm (((1 : ℝ) : ℂ) * Complex.I)
          have hv : ‖(((1 : ℝ) : ℂ) * Complex.I)‖ = 1 := by norm_num
          simpa [hφ', hv] using h
        have h2 : |φ' t| ≤ ‖fderiv ℝ f (γ t)‖ := by rw [← Real.norm_eq_abs]; exact h1
        simpa [hg, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h2 2
      have hgγc : Continuous fun t => g (γ t) := hgc.comp hγc
      have hreal : f z ^ 2 ≤ z.im * ∫ t in (0:ℝ)..z.im, g (γ t) := by
        have e : f z ^ 2 = (∫ t in (0:ℝ)..z.im, φ' t) ^ 2 := by rw [hftc]
        have hmono : ∫ t in (0:ℝ)..z.im, φ' t ^ 2 ≤ ∫ t in (0:ℝ)..z.im, g (γ t) :=
          intervalIntegral.integral_mono_on hzim.le ((hφc.pow 2).intervalIntegrable _ _)
            (hgγc.intervalIntegrable _ _) (fun t _ => hφle t)
        rw [e]
        calc (∫ t in (0:ℝ)..z.im, φ' t) ^ 2 ≤ z.im * ∫ t in (0:ℝ)..z.im, φ' t ^ 2 :=
              mixedPoincare_cs hφc hzim
          _ ≤ z.im * ∫ t in (0:ℝ)..z.im, g (γ t) := mul_le_mul_of_nonneg_left hmono hzim.le
      have hlin : ENNReal.ofReal (∫ t in (0:ℝ)..z.im, g (γ t)) ≤ G z.re := by
        rw [intervalIntegral.integral_of_le hzim.le, integral_Ioc_eq_integral_Ioo,
          ofReal_integral_eq_lintegral_ofReal ((hgγc.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
            (Eventually.of_forall fun t => by positivity)]
        calc ∫⁻ t in Ioo 0 z.im, ENNReal.ofReal (g (γ t))
            = ∫⁻ t in Ioo 0 z.im, F (γ t) := by
              refine setLIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_); rfl
          _ ≤ ∫⁻ t, F (γ t) := setLIntegral_le_lintegral _ _
          _ = G z.re := by rw [hG]; simp_rw [hγeq]
      rw [max_eq_left hzim.le]
      calc ENNReal.ofReal (f z ^ 2)
          ≤ ENNReal.ofReal (z.im * ∫ t in (0:ℝ)..z.im, g (γ t)) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal z.im * ENNReal.ofReal (∫ t in (0:ℝ)..z.im, g (γ t)) :=
            ENNReal.ofReal_mul hzim.le
        _ ≤ ENNReal.ofReal z.im * G z.re := mul_le_mul' le_rfl hlin
  -- integrate over the ball, using the vertical sections of the ball
  have hI : ∀ z ∈ Metric.ball p R, z.im ∈ Icc (p.im - R) (p.im + R) := by
    intro z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : |z.im - p.im| ≤ ‖z - p‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - p)
    have h2 := abs_le.1 (h1.trans hz.le)
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  have hsec : (p.im + R) - (p.im - R) = 2 * R := by ring
  have hmain : ∫⁻ z in Metric.ball p R, ENNReal.ofReal (f z ^ 2) ≤
      ENNReal.ofReal (2 * R) * (ENNReal.ofReal (|p.im| + R) * ∫⁻ z, ENNReal.ofReal (g z)) := by
    calc ∫⁻ z in Metric.ball p R, ENNReal.ofReal (f z ^ 2)
        = ∫⁻ z : ℂ, (Metric.ball p R).indicator (fun z => ENNReal.ofReal (f z ^ 2)) z :=
          (lintegral_indicator measurableSet_ball _).symm
      _ ≤ ∫⁻ z : ℂ, (ENNReal.ofReal (|p.im| + R) * G z.re) *
            (Icc (p.im - R) (p.im + R)).indicator 1 z.im := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ Metric.ball p R
          · have hzm : z.im ∈ Icc (p.im - R) (p.im + R) := hI z hz
            have hmax : ENNReal.ofReal (max z.im 0) ≤ ENNReal.ofReal (|p.im| + R) := by
              refine ENNReal.ofReal_le_ofReal (max_le ?_ (by positivity))
              linarith [(hI z hz).2, le_abs_self p.im]
            calc (Metric.ball p R).indicator (fun z => ENNReal.ofReal (f z ^ 2)) z
                = ENNReal.ofReal (f z ^ 2) := indicator_of_mem hz _
              _ ≤ ENNReal.ofReal (max z.im 0) * G z.re := hpt z
              _ ≤ ENNReal.ofReal (|p.im| + R) * G z.re := mul_le_mul' hmax le_rfl
              _ = (ENNReal.ofReal (|p.im| + R) * G z.re) *
                    (Icc (p.im - R) (p.im + R)).indicator 1 z.im := by
                  simp only [indicator_of_mem hzm, Pi.one_apply, mul_one]
          · rw [indicator_of_notMem hz]
            simp
      _ = ∫⁻ q : ℝ × ℝ, (ENNReal.ofReal (|p.im| + R) * G q.1) *
            (Icc (p.im - R) (p.im + R)).indicator 1 q.2 := by
          rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
            Complex.measurableEquivRealProd.symm.measurableEmbedding]
          rfl
      _ = (∫⁻ x, ENNReal.ofReal (|p.im| + R) * G x) *
            ∫⁻ y, (Icc (p.im - R) (p.im + R)).indicator 1 y := by
          rw [Measure.volume_eq_prod]
          exact lintegral_prod_mul (hGm.const_mul _).aemeasurable
            ((measurable_one.indicator measurableSet_Icc).aemeasurable)
      _ = ENNReal.ofReal (2 * R) * (ENNReal.ofReal (|p.im| + R) * ∫⁻ z, ENNReal.ofReal (g z)) := by
          rw [lintegral_const_mul _ hGm, hGint, lintegral_indicator_one measurableSet_Icc,
            Real.volume_Icc, hsec]
          ring
  have hI' : ∫ z in Metric.ball p R, f z ^ 2 =
      (∫⁻ z in Metric.ball p R, ENNReal.ofReal (f z ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by positivity)
      (hdiff.continuous.pow 2).aestronglyMeasurable
  have hgi : ∫ z, g z = (∫⁻ z, ENNReal.ofReal (g z)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by positivity)
      hgc.aestronglyMeasurable
  have hne : ENNReal.ofReal (2 * R) *
      (ENNReal.ofReal (|p.im| + R) * ∫⁻ z, ENNReal.ofReal (g z)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgfin.ne)
  have key := ENNReal.toReal_mono hne hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by positivity)] at key
  rw [← hI', ← hgi] at key
  calc ∫ x in Metric.ball p R, f x ^ 2 ≤ 2 * R * ((|p.im| + R) * ∫ x, g x) := key
    _ = 2 * R * (|p.im| + R) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by rw [hg]; ring

/-! ## 2. The logarithmic cutoff

The construction is `χ x = Φ (‖x - p‖²)` with `Φ s = ψ (log s / 2)` for `s > 0` (`Φ s = 0` for
`s ≤ 0`), where `ψ` is the affine rescaling of `Real.smoothTransition` onto the window
`[log (2r), log R]`. Off the flat part, `Φ` is a composition of smooth functions, hence smooth;
the flat point `s = 0` needs no separate argument because `log s / 2 ≤ log (2r)` for
`s ≤ (2r)²`, so `Φ` is *locally constant* there. -/

/-- Constant `K₀` bounding `‖deriv Real.smoothTransition‖`; `8` works. -/
def logCutoffConst : ℝ := 8

/-- `expNegInvGlue x = exp (-x⁻¹)` for `x > 0` (the defining branch). -/
lemma bubbleCutoff_expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) :
    expNegInvGlue x = Real.exp (-x⁻¹) := by
  simp [expNegInvGlue, hx.not_ge]

/-- The window length `L = log (R/(2r))` is positive when `0 < r` and `2r < R`. -/
lemma bubbleCutoff_log_pos {r R : ℝ} (hr : 0 < r) (h : 2 * r < R) :
    0 < Real.log (R / (2 * r)) := by
  refine Real.log_pos ?_
  rw [one_lt_div (by positivity : (0 : ℝ) < 2 * r)]
  linarith

lemma bubbleCutoff_differentiable_expNegInvGlue : Differentiable ℝ expNegInvGlue := by
  simpa using expNegInvGlue.differentiable_polynomial_eval_inv_mul (1 : Polynomial ℝ)

lemma bubbleCutoff_differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition := by
  have h1 := bubbleCutoff_differentiable_expNegInvGlue
  have h2 : Differentiable ℝ fun x : ℝ => expNegInvGlue (1 - x) :=
    h1.comp ((differentiable_const (c := (1 : ℝ))).sub differentiable_id)
  unfold Real.smoothTransition
  exact h1.div (h1.add h2) fun x => (Real.smoothTransition.pos_denom x).ne'

/-- The derivative of `expNegInvGlue` (from the mathlib API, with `p = 1`). -/
lemma bubbleCutoff_expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue (expNegInvGlue x / x ^ 2) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x
  have e : (fun y : ℝ => (1 : Polynomial ℝ).eval y⁻¹ * expNegInvGlue y) = expNegInvGlue := by
    funext y
    simp
  rw [e] at h
  refine h.congr_deriv ?_
  simp only [Polynomial.derivative_one, sub_zero, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, mul_one]
  rw [div_eq_mul_inv, inv_pow]
  ring

/-- Raw quotient-rule value of the derivative of `Real.smoothTransition`. -/
lemma bubbleCutoff_hasDerivAt_smoothTransition (x : ℝ) :
    HasDerivAt Real.smoothTransition
      ((expNegInvGlue x / x ^ 2 * (expNegInvGlue x + expNegInvGlue (1 - x)) -
          expNegInvGlue x *
            (expNegInvGlue x / x ^ 2 + -(expNegInvGlue (1 - x) / (1 - x) ^ 2))) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) x := by
  have h1 := bubbleCutoff_expNegInvGlue_hasDerivAt x
  have h2 : HasDerivAt (fun y : ℝ => expNegInvGlue (1 - y))
      (-(expNegInvGlue (1 - x) / (1 - x) ^ 2)) x := by
    have hsub : HasDerivAt (fun y : ℝ => 1 - y) (-1) x :=
      (hasDerivAt_id x).const_sub (1 : ℝ)
    have h3 : HasDerivAt (fun y : ℝ => expNegInvGlue (1 - y))
        (expNegInvGlue (1 - x) / (1 - x) ^ 2 * (-1)) x :=
      (bubbleCutoff_expNegInvGlue_hasDerivAt (1 - x)).comp x hsub
    convert h3 using 1
    ring
  unfold Real.smoothTransition
  exact h1.div (h1.add h2) (Real.smoothTransition.pos_denom x).ne'

/-- Division-free normal form: `s' = ab·(1/x² + 1/(1-x)²)/D²` for all `x`, where `a = e^{-1/x}`,
`b = e^{-1/(1-x)}`, `D = a + b` (Lean's junk values make the identity hold at the junctions). -/
lemma bubbleCutoff_deriv_smoothTransition_bound_form (x : ℝ) :
    deriv Real.smoothTransition x =
      (expNegInvGlue x * expNegInvGlue (1 - x) * (x ^ 2)⁻¹ +
          expNegInvGlue x * expNegInvGlue (1 - x) * ((1 - x) ^ 2)⁻¹) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 := by
  rw [(bubbleCutoff_hasDerivAt_smoothTransition x).deriv]
  congr 1
  first
    | ring
    | ring_nf

/-- The key ratio bound: `ab/D² ≤ e^{v-u}` with `a = e^{-u}`, `b = e^{-v}`, `D = a + b`. -/
lemma bubbleCutoff_ratio_le (u v : ℝ) :
    Real.exp (-u) * Real.exp (-v) / (Real.exp (-u) + Real.exp (-v)) ^ 2 ≤
      Real.exp (v - u) := by
  have h2 : Real.exp (-v) ^ 2 ≤ (Real.exp (-u) + Real.exp (-v)) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos (-v)).le
      (le_add_of_nonneg_left (Real.exp_pos (-u)).le) 2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Real.exp (-u) + Real.exp (-v)) ^ 2)]
  have e1 : Real.exp (-u) * Real.exp (-v) = Real.exp (v - u) * Real.exp (-v) ^ 2 := by
    rw [sq]
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [e1]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

/-- `|s'|` in terms of `u = 1/x`, `v = 1/(1-x)` in the window `0 < x < 1`. -/
lemma bubbleCutoff_abs_deriv_smoothTransition_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    |deriv Real.smoothTransition x| =
      ((x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2) *
        (expNegInvGlue x * expNegInvGlue (1 - x) /
          (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2) := by
  rw [bubbleCutoff_deriv_smoothTransition_bound_form]
  have ha : 0 ≤ expNegInvGlue x := expNegInvGlue.nonneg x
  have hb : 0 ≤ expNegInvGlue (1 - x) := expNegInvGlue.nonneg (1 - x)
  have hnum : 0 ≤ expNegInvGlue x * expNegInvGlue (1 - x) * (x ^ 2)⁻¹ +
      expNegInvGlue x * expNegInvGlue (1 - x) * ((1 - x) ^ 2)⁻¹ :=
    add_nonneg (mul_nonneg (mul_nonneg ha hb) (inv_nonneg.mpr (sq_nonneg x)))
      (mul_nonneg (mul_nonneg ha hb) (inv_nonneg.mpr (sq_nonneg (1 - x))))
  rw [abs_of_nonneg (div_nonneg hnum
    (pow_pos (Real.smoothTransition.pos_denom x) 2).le)]
  simp only [← inv_pow]
  first
    | ring
    | ring_nf

/-- `u²e^{-u} ≤ 4e^{-2}` (from `y e^{-y} ≤ e^{-1}` with `y = u/2`). -/
lemma bubbleCutoff_sq_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-u) ≤ 4 * Real.exp (-2) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (u / 2)
  have h2 : 0 ≤ u / 2 * Real.exp (-(u / 2)) := by positivity
  have h4 : (u / 2 * Real.exp (-(u / 2))) ^ 2 ≤ (Real.exp (-1)) ^ 2 :=
    pow_le_pow_left₀ h2 h 2
  have e1 : (u / 2 * Real.exp (-(u / 2))) ^ 2 = u ^ 2 / 4 * Real.exp (-u) := by
    have hexp : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, hexp]
    ring
  have e2 : (Real.exp (-1)) ^ 2 = Real.exp (-2) := by
    rw [sq, ← Real.exp_add, show (-1 : ℝ) + -1 = -2 by norm_num]
  rw [e1, e2] at h4
  calc u ^ 2 * Real.exp (-u) = 4 * (u ^ 2 / 4 * Real.exp (-u)) := by ring
    _ ≤ 4 * Real.exp (-2) := mul_le_mul_of_nonneg_left h4 (by norm_num)

/-- Core estimate: `(u²+v²)e^{v-u} ≤ 8` for `0 < v ≤ u ≤ 2`. -/
lemma bubbleCutoff_estimate {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) (hv2 : v ≤ 2) :
    (u ^ 2 + v ^ 2) * Real.exp (v - u) ≤ logCutoffConst := by
  have hu : 0 < u := lt_of_lt_of_le hv hvu
  have hA : u ^ 2 * Real.exp (v - u) ≤ 4 := by
    have h1 : u ^ 2 * Real.exp (-u) ≤ 4 * Real.exp (-2) :=
      bubbleCutoff_sq_mul_exp_neg_le hu.le
    have h2 : Real.exp v ≤ Real.exp 2 := Real.exp_le_exp.mpr hv2
    calc u ^ 2 * Real.exp (v - u) = u ^ 2 * Real.exp (-u) * Real.exp v := by
          rw [Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
          ring
      _ ≤ 4 * Real.exp (-2) * Real.exp 2 :=
          mul_le_mul h1 h2 (Real.exp_pos v).le (by positivity)
      _ = 4 := by
          rw [mul_assoc, ← Real.exp_add, show (-2 : ℝ) + 2 = 0 by norm_num, Real.exp_zero,
            mul_one]
  have hB : v ^ 2 * Real.exp (v - u) ≤ 4 := by
    have h1 : Real.exp (v - u) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    calc v ^ 2 * Real.exp (v - u) ≤ v ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = v ^ 2 := by ring
      _ ≤ 4 := by nlinarith
  calc (u ^ 2 + v ^ 2) * Real.exp (v - u)
      = u ^ 2 * Real.exp (v - u) + v ^ 2 * Real.exp (v - u) := by ring
    _ ≤ 4 + 4 := add_le_add hA hB
    _ = logCutoffConst := by norm_num [logCutoffConst]

/-- The derivative bound in the window `0 < x < 1`: `|s'| ≤ 8`. Writing `u = 1/x > 1` and
`v = 1/(1-x)`, the bound is `(u²+v²)e^{±(v-u)} ≤ 8` by `bubbleCutoff_estimate`. -/
lemma bubbleCutoff_abs_deriv_smoothTransition_le_window {x : ℝ} (hx : 0 < x) (h1 : x < 1) :
    |deriv Real.smoothTransition x| ≤ logCutoffConst := by
  have h1x : 0 < 1 - x := by linarith
  rw [bubbleCutoff_abs_deriv_smoothTransition_eq hx h1]
  rcases le_total x (1 / 2) with h2 | h2
  · have hv2 : (1 - x)⁻¹ ≤ 2 := by
      calc (1 - x)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := (inv_le_inv₀ h1x (by norm_num)).mpr (by linarith)
        _ = 2 := by norm_num
    have hvu : (1 - x)⁻¹ ≤ x⁻¹ := (inv_le_inv₀ h1x hx).mpr (by linarith)
    have hv : 0 < (1 - x)⁻¹ := inv_pos.mpr h1x
    have hratio : expNegInvGlue x * expNegInvGlue (1 - x) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 ≤
        Real.exp ((1 - x)⁻¹ - x⁻¹) := by
      rw [bubbleCutoff_expNegInvGlue_of_pos hx, bubbleCutoff_expNegInvGlue_of_pos h1x]
      exact bubbleCutoff_ratio_le x⁻¹ (1 - x)⁻¹
    calc ((x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2) * (expNegInvGlue x * expNegInvGlue (1 - x) /
          (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2)
        ≤ ((x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2) * Real.exp ((1 - x)⁻¹ - x⁻¹) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = ((x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2) * Real.exp ((1 - x)⁻¹ - x⁻¹) := by ring
      _ ≤ logCutoffConst := bubbleCutoff_estimate hv hvu hv2
  · have hu2 : x⁻¹ ≤ 2 := by
      calc x⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := (inv_le_inv₀ hx (by norm_num)).mpr h2
        _ = 2 := by norm_num
    have hvu : x⁻¹ ≤ (1 - x)⁻¹ := (inv_le_inv₀ hx h1x).mpr (by linarith)
    have hv : 0 < x⁻¹ := inv_pos.mpr hx
    have hratio : expNegInvGlue x * expNegInvGlue (1 - x) /
        (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2 ≤
        Real.exp (x⁻¹ - (1 - x)⁻¹) := by
      rw [bubbleCutoff_expNegInvGlue_of_pos hx, bubbleCutoff_expNegInvGlue_of_pos h1x]
      simpa only [mul_comm, add_comm] using bubbleCutoff_ratio_le (1 - x)⁻¹ x⁻¹
    calc ((x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2) * (expNegInvGlue x * expNegInvGlue (1 - x) /
          (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2)
        ≤ ((x⁻¹) ^ 2 + ((1 - x)⁻¹) ^ 2) * Real.exp (x⁻¹ - (1 - x)⁻¹) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (((1 - x)⁻¹) ^ 2 + (x⁻¹) ^ 2) * Real.exp (x⁻¹ - (1 - x)⁻¹) := by ring
      _ ≤ logCutoffConst := bubbleCutoff_estimate hv hvu hu2

/-- The bound `|s'| ≤ 8` away from the junctions `x = 0, 1`. -/
lemma bubbleCutoff_abs_deriv_smoothTransition_le_of_ne {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    |deriv Real.smoothTransition x| ≤ logCutoffConst := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [((Filter.EventuallyEq.hasDerivAt_iff hev).mpr (hasDerivAt_const (c := (0 : ℝ)) x)).deriv,
      abs_zero]
    norm_num [logCutoffConst]
  · exact absurd hx hx0
  · rcases lt_trichotomy x 1 with h1 | h1 | h1
    · exact bubbleCutoff_abs_deriv_smoothTransition_le_window hx h1
    · exact absurd h1 hx1
    · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds h1] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [((Filter.EventuallyEq.hasDerivAt_iff hev).mpr (hasDerivAt_const (c := (1 : ℝ)) x)).deriv,
        abs_zero]
      norm_num [logCutoffConst]

/-- **`logCutoffConst` bounds the derivative of `Real.smoothTransition`** everywhere. At the
junctions `0` and `1` the closed form of
`bubbleCutoff_deriv_smoothTransition_bound_form` vanishes (both because the function is flat
there), so those two points are handled by direct computation. -/
lemma bubbleCutoff_abs_deriv_smoothTransition_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ logCutoffConst := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [bubbleCutoff_deriv_smoothTransition_bound_form]
    simp [logCutoffConst]
  · rcases eq_or_ne x 1 with rfl | hx1
    · rw [bubbleCutoff_deriv_smoothTransition_bound_form]
      simp [logCutoffConst]
    · exact bubbleCutoff_abs_deriv_smoothTransition_le_of_ne hx0 hx1

/-! ### The cutoff functions -/

/-- The affine rescaling of `Real.smoothTransition` onto the window `[log (2r), log R]`. -/
def logCutoffProfile (r R : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((t - Real.log (2 * r)) * (Real.log (R / (2 * r)))⁻¹)

/-- The radial profile `Φ`, equal to `0` for `s ≤ 0` and `ψ (log s / 2)` for `s > 0`. -/
def logCutoffRadial (r R : ℝ) : ℝ → ℝ :=
  fun s => if s ≤ 0 then 0 else logCutoffProfile r R (Real.log s / 2)

/-- `χ x = Φ (‖x - p‖²)`. -/
def logCutoff (p : ℂ) (r R : ℝ) : ℂ → ℝ :=
  fun x => logCutoffRadial r R (‖x - p‖ ^ 2)

lemma bubbleCutoff_contDiff_logCutoffProfile (r R : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logCutoffProfile r R) := by
  unfold logCutoffProfile
  exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
    ((contDiff_id.sub contDiff_const).mul contDiff_const)

lemma bubbleCutoff_differentiable_logCutoffProfile (r R : ℝ) :
    Differentiable ℝ (logCutoffProfile r R) := by
  unfold logCutoffProfile
  exact bubbleCutoff_differentiable_smoothTransition.comp
    ((differentiable_id.sub (differentiable_const (c := Real.log (2 * r)))).mul_const _)

/-- `Φ` vanishes identically on the ball of radius `(2r)²` around `0`: this makes it smooth
(and locally constant) at the junction point `s = 0`. -/
lemma bubbleCutoff_logCutoffRadial_eq_zero {r R : ℝ} (hr : 0 < r) (h : 2 * r < R) {s : ℝ}
    (hs : s < (2 * r) ^ 2) : logCutoffRadial r R s = 0 := by
  have hL : 0 < Real.log (R / (2 * r)) := bubbleCutoff_log_pos hr h
  by_cases h0 : s ≤ 0
  · simp only [logCutoffRadial, if_pos h0]
  · have hspos : 0 < s := lt_of_not_ge h0
    have hsle : Real.log s ≤ Real.log ((2 * r) ^ 2) :=
      (Real.log_le_log_iff hspos (by positivity)).mpr hs.le
    have hfac : Real.log s / 2 - Real.log (2 * r) ≤ 0 := by
      have h2 : Real.log s ≤ 2 * Real.log (2 * r) := by
        have h3 := hsle
        rwa [Real.log_pow, Nat.cast_ofNat] at h3
      have h4 : Real.log s - 2 * Real.log (2 * r) ≤ 0 := sub_nonpos.mpr h2
      have h5 : Real.log s / 2 - Real.log (2 * r) =
          (Real.log s - 2 * Real.log (2 * r)) / 2 := by ring
      rw [h5]
      exact div_nonpos_of_nonpos_of_nonneg h4 (by norm_num)
    simp only [logCutoffRadial, if_neg h0, logCutoffProfile]
    exact Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg hfac (inv_nonneg.mpr hL.le))

/-- `Φ` is smooth: smooth off the flat point `s = 0`, and locally constant there. -/
lemma bubbleCutoff_contDiff_logCutoffRadial {r R : ℝ} (hr : 0 < r) (h : 2 * r < R) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logCutoffRadial r R) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases lt_trichotomy s 0 with hs | hs | hs
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hs] with t ht
    simp only [logCutoffRadial, if_pos ht.le]
  · subst hs
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < (2 * r) ^ 2 by positivity)] with t ht
    exact bubbleCutoff_logCutoffRadial_eq_zero hr h ht
  · refine (((bubbleCutoff_contDiff_logCutoffProfile r R).contDiffAt.comp s
      (((Real.contDiffAt_log (x := s)).2 hs.ne').div_const 2))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hs] with t ht
    simp only [logCutoffRadial, Function.comp_def, if_neg ht.not_ge]

lemma bubbleCutoff_differentiable_logCutoffRadial {r R : ℝ} (hr : 0 < r) (h : 2 * r < R) :
    Differentiable ℝ (logCutoffRadial r R) := by
  intro s
  rcases lt_trichotomy s 0 with hs | hs | hs
  · refine (differentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_lt_nhds hs] with t ht
    simp only [logCutoffRadial, if_pos ht.le]
  · subst hs
    refine (differentiableAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < (2 * r) ^ 2 by positivity)] with t ht
    exact bubbleCutoff_logCutoffRadial_eq_zero hr h ht
  · refine ((bubbleCutoff_differentiable_logCutoffProfile r R (Real.log s / 2)).comp s
      ((Real.differentiableAt_log hs.ne').div_const 2)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hs] with t ht
    simp only [logCutoffRadial, Function.comp_def, if_neg ht.not_ge]

/-- Derivative bound for the rescaled profile: the affine rescaling divides the derivative by
the window length `L = log (R/(2r))`. -/
lemma bubbleCutoff_abs_deriv_logCutoffProfile_le {r R : ℝ} (hr : 0 < r) (h : 2 * r < R)
    (t : ℝ) : ‖deriv (logCutoffProfile r R) t‖ ≤ logCutoffConst / Real.log (R / (2 * r)) := by
  have hL : 0 < Real.log (R / (2 * r)) := bubbleCutoff_log_pos hr h
  have hder : HasDerivAt (fun y : ℝ => (y - Real.log (2 * r)) * (Real.log (R / (2 * r)))⁻¹)
      ((Real.log (R / (2 * r)))⁻¹) t := by
    have h := ((hasDerivAt_id t).sub_const (Real.log (2 * r))).mul_const
      ((Real.log (R / (2 * r)))⁻¹)
    exact h.congr_deriv (by ring)
  have hder' : HasDerivAt (logCutoffProfile r R)
      (deriv Real.smoothTransition ((t - Real.log (2 * r)) * (Real.log (R / (2 * r)))⁻¹) *
        (Real.log (R / (2 * r)))⁻¹) t := by
    have hψ : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition ((t - Real.log (2 * r)) * (Real.log (R / (2 * r)))⁻¹))
        ((t - Real.log (2 * r)) * (Real.log (R / (2 * r)))⁻¹) :=
      (bubbleCutoff_differentiable_smoothTransition _).hasDerivAt
    exact hψ.comp t hder
  have hd : deriv (logCutoffProfile r R) t =
      deriv Real.smoothTransition ((t - Real.log (2 * r)) * (Real.log (R / (2 * r)))⁻¹) *
        (Real.log (R / (2 * r)))⁻¹ := by
    simpa only [logCutoffProfile] using hder'.deriv
  rw [hd, norm_mul]
  simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hL]
  calc |deriv Real.smoothTransition _| * (Real.log (R / (2 * r)))⁻¹
      ≤ logCutoffConst * (Real.log (R / (2 * r)))⁻¹ :=
        mul_le_mul_of_nonneg_right (bubbleCutoff_abs_deriv_smoothTransition_le _) (by positivity)
    _ = logCutoffConst / Real.log (R / (2 * r)) := by simp only [div_eq_mul_inv]

/-- Derivative bound for the radial profile on `s > 0`, with the extra factor `1/(2s)` coming
from `d/ds log s = 1/s`. -/
lemma bubbleCutoff_deriv_logCutoffRadial_le {r R : ℝ} (hr : 0 < r) (h : 2 * r < R) :
    ∀ s : ℝ, 0 < s → ‖deriv (logCutoffRadial r R) s‖ ≤
      logCutoffConst / (Real.log (R / (2 * r)) * 2 * s) := by
  intro s hs
  have hL : 0 < Real.log (R / (2 * r)) := bubbleCutoff_log_pos hr h
  have hev : logCutoffRadial r R =ᶠ[𝓝 s] fun t => logCutoffProfile r R (Real.log t / 2) := by
    filter_upwards [eventually_gt_nhds hs] with t ht
    simp only [logCutoffRadial, if_neg (not_le.mpr ht)]
  have hder : HasDerivAt (fun t : ℝ => logCutoffProfile r R (Real.log t / 2))
      (deriv (logCutoffProfile r R) (Real.log s / 2) * (2 * s)⁻¹) s := by
    have hlog : HasDerivAt (fun t : ℝ => Real.log t / 2) ((2 * s)⁻¹) s := by
      have h0 : HasDerivAt (fun t : ℝ => Real.log t / 2) (s⁻¹ / 2) s :=
        (Real.hasDerivAt_log hs.ne').div_const 2
      have e : s⁻¹ / 2 = (2 * s)⁻¹ := by
        first
          | (simp only [div_eq_mul_inv]; field_simp; ring)
          | (field_simp; ring)
          | ring_nf
      rwa [e] at h0
    have hcomp :=
      (bubbleCutoff_differentiable_logCutoffProfile r R (Real.log s / 2)).hasDerivAt.comp s hlog
    simpa only [Function.comp_def] using hcomp
  have hd : deriv (logCutoffRadial r R) s =
      deriv (logCutoffProfile r R) (Real.log s / 2) * (2 * s)⁻¹ :=
    ((Filter.EventuallyEq.hasDerivAt_iff hev).mpr hder).deriv
  rw [hd, norm_mul]
  have hψb := bubbleCutoff_abs_deriv_logCutoffProfile_le (r := r) (R := R) hr h (Real.log s / 2)
  have h2s : ‖((2 : ℝ) * s)⁻¹‖ = (2 * s)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < (2 : ℝ) * s))]
  rw [h2s]
  calc ‖deriv (logCutoffProfile r R) (Real.log s / 2)‖ * (2 * s)⁻¹
      ≤ (logCutoffConst / Real.log (R / (2 * r))) * (2 * s)⁻¹ :=
        mul_le_mul_of_nonneg_right hψb (by positivity)
    _ = logCutoffConst / (Real.log (R / (2 * r)) * 2 * s) := by
        first
          | (simp only [div_eq_mul_inv]; field_simp; ring)
          | (field_simp; ring)
          | ring_nf

lemma bubbleCutoff_logCutoff_mem_Icc (p : ℂ) (r R : ℝ) (x : ℂ) :
    logCutoff p r R x ∈ Set.Icc 0 1 := by
  by_cases hs : ‖x - p‖ ^ 2 ≤ 0
  · simp only [logCutoff, logCutoffRadial, if_pos hs]
    exact ⟨le_rfl, zero_le_one⟩
  · simp only [logCutoff, logCutoffRadial, if_neg hs, logCutoffProfile]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma bubbleCutoff_logCutoff_eq_zero (p : ℂ) {r R : ℝ} (hr : 0 < r) (h : 2 * r < R) {x : ℂ}
    (hx : ‖x - p‖ ≤ 2 * r) : logCutoff p r R x = 0 := by
  have hL : 0 < Real.log (R / (2 * r)) := bubbleCutoff_log_pos hr h
  have h2r : 0 < 2 * r := by linarith
  by_cases hs : ‖x - p‖ ^ 2 ≤ 0
  · simp only [logCutoff, logCutoffRadial, if_pos hs]
  · have hspos : 0 < ‖x - p‖ ^ 2 := lt_of_not_ge hs
    have hsle : ‖x - p‖ ^ 2 ≤ (2 * r) ^ 2 := by nlinarith [norm_nonneg (x - p)]
    have hlog : Real.log (‖x - p‖ ^ 2) / 2 ≤ Real.log (2 * r) := by
      have h1 : Real.log (‖x - p‖ ^ 2) ≤ Real.log ((2 * r) ^ 2) :=
        (Real.log_le_log_iff hspos (by positivity)).mpr hsle
      have hp : Real.log ((2 * r) ^ 2) = 2 * Real.log (2 * r) := Real.log_pow (2 * r) 2
      rw [hp] at h1
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    simp only [logCutoff, logCutoffRadial, if_neg hs, logCutoffProfile]
    exact Real.smoothTransition.zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (inv_nonneg.mpr hL.le))

lemma bubbleCutoff_logCutoff_eq_one (p : ℂ) {r R : ℝ} (hr : 0 < r) (h : 2 * r < R) {x : ℂ}
    (hx : R ≤ ‖x - p‖) : logCutoff p r R x = 1 := by
  have hL : 0 < Real.log (R / (2 * r)) := bubbleCutoff_log_pos hr h
  have hR : 0 < R := by linarith
  have hspos : 0 < ‖x - p‖ ^ 2 := by
    have h1 : 0 < ‖x - p‖ := lt_of_lt_of_le hR hx
    positivity
  have hsle : R ^ 2 ≤ ‖x - p‖ ^ 2 := by nlinarith [norm_nonneg (x - p)]
  have hlog : Real.log (2 * r) + Real.log (R / (2 * r)) ≤ Real.log (‖x - p‖ ^ 2) / 2 := by
    have h1 : Real.log (R ^ 2) ≤ Real.log (‖x - p‖ ^ 2) :=
      (Real.log_le_log_iff (by positivity) hspos).mpr hsle
    have hp : Real.log (R ^ 2) = 2 * Real.log R := Real.log_pow R 2
    rw [hp] at h1
    have h2 : Real.log R = Real.log (2 * r) + Real.log (R / (2 * r)) := by
      rw [← Real.log_mul (by positivity : (2 : ℝ) * r ≠ 0) (by positivity : R / (2 * r) ≠ 0)]
      congr 1
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm (2 * r) R, mul_assoc,
        mul_comm (2 * r) ((2 * r)⁻¹), inv_mul_cancel₀ (by positivity : (2 : ℝ) * r ≠ 0),
        mul_one]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  simp only [logCutoff, logCutoffRadial, if_neg (not_le.mpr hspos), logCutoffProfile]
  refine Real.smoothTransition.one_of_one_le ?_
  have h3 : (1 : ℝ) ≤ (Real.log (‖x - p‖ ^ 2) / 2 - Real.log (2 * r)) *
      (Real.log (R / (2 * r)))⁻¹ := by
    have h4 : (Real.log (R / (2 * r)))⁻¹ * Real.log (R / (2 * r)) ≤
        (Real.log (R / (2 * r)))⁻¹ *
          (Real.log (‖x - p‖ ^ 2) / 2 - Real.log (2 * r)) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hL.le)
    rw [inv_mul_cancel₀ (ne_of_gt hL), mul_comm] at h4
    exact h4
  exact h3

/-- **Derivative bound for the cutoff.** -/
lemma bubbleCutoff_fderiv_logCutoff_le (p : ℂ) {r R : ℝ} (hr : 0 < r) (h : 2 * r < R) (x : ℂ) :
    ‖fderiv ℝ (logCutoff p r R) x‖ ≤
      logCutoffConst / (Real.log (R / (2 * r)) * ‖x - p‖) := by
  have hL : 0 < Real.log (R / (2 * r)) := bubbleCutoff_log_pos hr h
  rcases eq_or_ne x p with hxp | hne
  · rw [hxp]
    have hev : logCutoff p r R =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds p (show (0 : ℝ) < 2 * r by linarith)] with y hy
      rw [Metric.mem_ball, Complex.dist_eq] at hy
      exact bubbleCutoff_logCutoff_eq_zero p hr h (by simpa only [norm_sub_rev] using hy.le)
    rw [((Filter.EventuallyEq.hasFDerivAt_iff hev).mpr (hasFDerivAt_const (0 : ℝ) p)).fderiv,
      norm_zero]
    exact div_nonneg (by norm_num [logCutoffConst]) (mul_nonneg hL.le (norm_nonneg _))
  · have hρ : HasFDerivAt (fun y : ℂ => ‖y - p‖ ^ 2)
        ((2 : ℝ) • innerSL ℝ (x - p)) x := by
      have h1 : HasFDerivAt (fun y : ℂ => y - p) (1 : ℂ →L[ℝ] ℂ) x :=
        (hasFDerivAt_id x).sub_const p
      have h2 := HasFDerivAt.norm_sq h1
      have h3 : (2 : ℕ) • ((innerSL ℝ (x - p)).comp (1 : ℂ →L[ℝ] ℂ)) =
          (2 : ℝ) • innerSL ℝ (x - p) := by
        rw [← Nat.cast_smul_eq_nsmul (R := ℝ) 2]
        congr 1
      simpa only [h3] using h2
    have hρnorm : ‖fderiv ℝ (fun y : ℂ => ‖y - p‖ ^ 2) x‖ ≤ 2 * ‖x - p‖ := by
      have hnorm : ‖fderiv ℝ (fun y : ℂ => ‖y - p‖ ^ 2) x‖ = 2 * ‖x - p‖ := by
        rw [hρ.fderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          innerSL_apply_norm]
      rw [hnorm]
    have hχ : fderiv ℝ (logCutoff p r R) x =
        (fderiv ℝ (logCutoffRadial r R) (‖x - p‖ ^ 2)).comp
          (fderiv ℝ (fun y : ℂ => ‖y - p‖ ^ 2) x) := by
      have hcomp : HasFDerivAt ((logCutoffRadial r R) ∘ fun y : ℂ => ‖y - p‖ ^ 2)
          ((fderiv ℝ (logCutoffRadial r R) (‖x - p‖ ^ 2)).comp
            (fderiv ℝ (fun y : ℂ => ‖y - p‖ ^ 2) x)) x :=
        HasFDerivAt.comp (f := fun y : ℂ => ‖y - p‖ ^ 2) (x := x)
          (g := logCutoffRadial r R)
          (hg := ((bubbleCutoff_differentiable_logCutoffRadial hr h) (‖x - p‖ ^ 2)).hasFDerivAt)
          (hf := (hρ.differentiableAt.hasFDerivAt))
      rw [show logCutoff p r R = (logCutoffRadial r R) ∘ fun y : ℂ => ‖y - p‖ ^ 2 from rfl]
      exact hcomp.fderiv
    have hLne : Real.log (R / (2 * r)) ≠ 0 := ne_of_gt hL
    have hnne : ‖x - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
    calc ‖fderiv ℝ (logCutoff p r R) x‖
        ≤ ‖fderiv ℝ (logCutoffRadial r R) (‖x - p‖ ^ 2)‖ *
            ‖fderiv ℝ (fun y : ℂ => ‖y - p‖ ^ 2) x‖ := by
          rw [hχ]
          exact ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (logCutoffRadial r R) (‖x - p‖ ^ 2))
            (fderiv ℝ (fun y : ℂ => ‖y - p‖ ^ 2) x)
      _ ≤ ‖deriv (logCutoffRadial r R) (‖x - p‖ ^ 2)‖ * (2 * ‖x - p‖) := by
          have h1 : ‖fderiv ℝ (logCutoffRadial r R) (‖x - p‖ ^ 2)‖ =
              ‖deriv (logCutoffRadial r R) (‖x - p‖ ^ 2)‖ := by
            rw [← norm_deriv_eq_norm_fderiv]
          rw [h1]
          exact mul_le_mul_of_nonneg_left hρnorm
            (norm_nonneg (deriv (logCutoffRadial r R) (‖x - p‖ ^ 2)))
      _ ≤ (logCutoffConst / (Real.log (R / (2 * r)) * 2 * ‖x - p‖ ^ 2)) * (2 * ‖x - p‖) :=
          mul_le_mul_of_nonneg_right
            (bubbleCutoff_deriv_logCutoffRadial_le hr h _
              (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2))
            (by positivity)
      _ = logCutoffConst / (Real.log (R / (2 * r)) * ‖x - p‖) := by
          rw [pow_two]
          first
            | field_simp
            | (field_simp; ring)
            | ring_nf

end QuantumZipper.K3
