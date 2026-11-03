/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.ReverseODE at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Loewner.Reverse
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Existence, uniqueness and basic properties of the reverse Loewner flow

Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, Section 1. See `FOUNDATIONS.md` §4.

For `W` continuous, `z` in the upper half-plane and `T ≥ 0`, we show:

* `exists_isReverseSol`, `isReverseSol_unique`, `isReverseSol_restrict`: `IsReverseSol W z T`
  has a unique solution, and solutions restrict to shorter time intervals.
* `revMap_eq`: `revMap` (defined by choice) always computes this unique solution.
* `im_le_im_revMap`, `monotoneOn_im_revMap`: the flow only moves up in `ℍ`.
* `norm_revMap_sub_le`: a quantitative bound on how far the flow has moved.

## Method

Writing `v_t := u_t + W_t`, `IsReverseSol` becomes the genuine (non-autonomous, but
continuous-in-`t`) ODE `v' = -2/(v - W_t)`, `v_0 = z`. Since `Im(-2/(v-W_t)) =
2 Im(v)/|v-W_t|² ≥ 0`, any solution's imaginary part is nondecreasing
(`isReverseSol_monotoneOn_im`); this is the key fact used throughout. For existence, the
field is truncated by clamping `Im v` up to `δ := z.im` (`clampIm`, `revVFTrunc`), which
makes it globally bounded and Lipschitz; Picard-Lindelöf then gives a global solution of the
truncated equation, and the same monotonicity argument (run on the truncated field, whose
truncated derivative is *always* nonnegative) shows the clamp is never active, so the
truncated solution solves the true equation. Uniqueness is Gronwall/Lipschitz comparison on
`{Im ≥ z.im}`, using mathlib's `ODE_solution_unique_of_mem_Icc_right`.
-/

noncomputable section

open Complex Filter MeasureTheory intervalIntegral
open scoped Topology NNReal

namespace QuantumZipper

/-! ### Auxiliary: the reverse-flow vector field, truncated to be globally Lipschitz -/

section Aux

/-- `y` with its imaginary part clamped up to at least `δ`, as a purely imaginary shift of
`y` (this presentation makes continuity in `y` immediate). -/
private def clampIm (δ : ℝ) (y : ℂ) : ℂ := y + ((max y.im δ - y.im : ℝ) : ℂ) * Complex.I

private lemma clampIm_re (δ : ℝ) (y : ℂ) : (clampIm δ y).re = y.re := by
  simp [clampIm]

private lemma clampIm_im (δ : ℝ) (y : ℂ) : (clampIm δ y).im = max y.im δ := by
  simp [clampIm]

private lemma continuous_clampIm (δ : ℝ) : Continuous (clampIm δ) := by
  unfold clampIm; fun_prop

private lemma dist_clampIm_le (δ : ℝ) (y₁ y₂ : ℂ) :
    ‖clampIm δ y₁ - clampIm δ y₂‖ ≤ 2 * ‖y₁ - y₂‖ := by
  have hre : (clampIm δ y₁ - clampIm δ y₂).re = (y₁ - y₂).re := by
    simp [Complex.sub_re, clampIm_re]
  have him : |(clampIm δ y₁ - clampIm δ y₂).im| ≤ |(y₁ - y₂).im| := by
    have h := abs_max_sub_max_le_max y₁.im δ y₂.im δ
    simp only [Complex.sub_im, clampIm_im]
    simpa using h
  calc ‖clampIm δ y₁ - clampIm δ y₂‖
      ≤ |(clampIm δ y₁ - clampIm δ y₂).re| + |(clampIm δ y₁ - clampIm δ y₂).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |(y₁ - y₂).re| + |(y₁ - y₂).im| := by rw [hre]; gcongr
    _ ≤ ‖y₁ - y₂‖ + ‖y₁ - y₂‖ :=
        add_le_add (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
    _ = 2 * ‖y₁ - y₂‖ := by ring

private lemma le_norm_clampIm_sub (δ : ℝ) (w : ℝ) (y : ℂ) :
    δ ≤ ‖clampIm δ y - (w : ℂ)‖ := by
  have h1 : (clampIm δ y - (w : ℂ)).im = max y.im δ := by simp [Complex.sub_im, clampIm_im]
  calc δ ≤ max y.im δ := le_max_right _ _
    _ = (clampIm δ y - (w : ℂ)).im := h1.symm
    _ ≤ ‖clampIm δ y - (w : ℂ)‖ := Complex.im_le_norm _

/-- The reverse-flow vector field `-2/(y - W t)` with `y`'s imaginary part clamped up to `δ`,
so that it is globally bounded and Lipschitz in `y`. -/
private def revVFTrunc (W : ℝ → ℝ) (δ : ℝ) (t : ℝ) (y : ℂ) : ℂ :=
  -2 / (clampIm δ y - (W t : ℂ))

private lemma norm_revVFTrunc_le (W : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (y : ℂ) :
    ‖revVFTrunc W δ t y‖ ≤ 2 / δ := by
  have h1 : δ ≤ ‖clampIm δ y - (W t : ℂ)‖ := le_norm_clampIm_sub δ (W t) y
  have h1' : 0 < ‖clampIm δ y - (W t : ℂ)‖ := lt_of_lt_of_le hδ h1
  have h2 : ‖revVFTrunc W δ t y‖ = ‖(-2 : ℂ)‖ / ‖clampIm δ y - (W t : ℂ)‖ := by
    rw [revVFTrunc, norm_div]
  rw [h2, show ‖(-2 : ℂ)‖ = 2 from by norm_num, div_le_div_iff₀ h1' hδ]
  nlinarith [h1]

private lemma continuous_revVFTrunc (W : ℝ → ℝ) (hW : Continuous W) (δ : ℝ) (hδ : 0 < δ)
    (y : ℂ) : Continuous fun t => revVFTrunc W δ t y := by
  have hden : Continuous fun t => clampIm δ y - (W t : ℂ) :=
    continuous_const.sub (Complex.continuous_ofReal.comp hW)
  have hne : ∀ t, clampIm δ y - (W t : ℂ) ≠ 0 := by
    intro t h
    have h1 := le_norm_clampIm_sub δ (W t) y
    rw [h, norm_zero] at h1
    linarith
  exact continuous_const.div hden hne

/-- The imaginary part of the truncated field is always `≥ 0`, because the clamp forces the
imaginary part of its argument to be `≥ δ > 0`, regardless of `y`. -/
private lemma im_revVFTrunc_nonneg (W : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (y : ℂ) :
    0 ≤ (revVFTrunc W δ t y).im := by
  set w := clampIm δ y - (W t : ℂ) with hwdef
  have hwim : δ ≤ w.im := by
    have h := le_norm_clampIm_sub δ (W t) y
    have h2 : (clampIm δ y - (W t : ℂ)).im = max y.im δ := by simp [Complex.sub_im, clampIm_im]
    rw [hwdef, h2]
    exact le_max_right _ _
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hwim; simp at hwim; linarith
  have hrw : revVFTrunc W δ t y = (-2 : ℂ) * w⁻¹ := by
    rw [revVFTrunc, ← hwdef, div_eq_mul_inv]
  have h1 : ((-2 : ℂ) * w⁻¹).im = (-2) * w⁻¹.im := by simp [Complex.mul_im]
  rw [hrw, h1, Complex.inv_im]
  have hnormsq : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
  have heq : (-2 : ℝ) * (-w.im / Complex.normSq w) = 2 * w.im / Complex.normSq w := by ring
  rw [heq]
  exact div_nonneg (by linarith) hnormsq

private lemma lipschitzWith_revVFTrunc (W : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    LipschitzWith (⟨4 / δ ^ 2, by positivity⟩ : ℝ≥0) (revVFTrunc W δ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro y₁ y₂
  show dist (revVFTrunc W δ t y₁) (revVFTrunc W δ t y₂) ≤ (4 / δ ^ 2) * dist y₁ y₂
  rw [dist_eq_norm, dist_eq_norm]
  set w₁ := clampIm δ y₁ - (W t : ℂ) with hw1def
  set w₂ := clampIm δ y₂ - (W t : ℂ) with hw2def
  have hw1 : δ ≤ ‖w₁‖ := le_norm_clampIm_sub δ (W t) y₁
  have hw2 : δ ≤ ‖w₂‖ := le_norm_clampIm_sub δ (W t) y₂
  have hw10 : w₁ ≠ 0 := by intro h; rw [h, norm_zero] at hw1; linarith
  have hw20 : w₂ ≠ 0 := by intro h; rw [h, norm_zero] at hw2; linarith
  have hrw : revVFTrunc W δ t y₁ - revVFTrunc W δ t y₂ = 2 * (w₁ - w₂) / (w₁ * w₂) := by
    show (-2 : ℂ) / w₁ - (-2 : ℂ) / w₂ = 2 * (w₁ - w₂) / (w₁ * w₂)
    field_simp
    ring
  have hsub : ‖w₁ - w₂‖ ≤ 2 * ‖y₁ - y₂‖ := by
    have heq : w₁ - w₂ = clampIm δ y₁ - clampIm δ y₂ := by rw [hw1def, hw2def]; ring
    rw [heq]
    exact dist_clampIm_le δ y₁ y₂
  have hprod : δ ^ 2 ≤ ‖w₁‖ * ‖w₂‖ := by nlinarith [hw1, hw2, hδ]
  have step1 : 2 * ‖w₁ - w₂‖ * δ ^ 2 ≤ 4 * ‖y₁ - y₂‖ * δ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hsub]) (sq_nonneg δ)
  have step2 : 4 * ‖y₁ - y₂‖ * δ ^ 2 ≤ 4 * ‖y₁ - y₂‖ * (‖w₁‖ * ‖w₂‖) :=
    mul_le_mul_of_nonneg_left hprod (by positivity)
  rw [hrw, norm_div, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num,
    div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [step1, step2]

/-- `Icc a b` is a neighborhood of `t` within `Ici t`, when `a ≤ t < b`. -/
private lemma icc_mem_nhdsWithin_Ici {a b t : ℝ} (ht1 : a ≤ t) (ht2 : t < b) :
    Set.Icc a b ∈ 𝓝[Set.Ici t] t := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio b, isOpen_Iio, ht2, fun x hx => ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici] at hx
  exact ⟨le_trans ht1 hx.2, le_of_lt hx.1⟩

/-- `Icc a b` is a neighborhood of `t` within `Ioi t`, when `a ≤ t < b`. -/
private lemma icc_mem_nhdsWithin_Ioi {a b t : ℝ} (ht1 : a ≤ t) (ht2 : t < b) :
    Set.Icc a b ∈ 𝓝[Set.Ioi t] t := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio b, isOpen_Iio, ht2, fun x hx => ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi] at hx
  exact ⟨le_trans ht1 hx.2.le, le_of_lt hx.1⟩

end Aux

/-! ### Any solution has nondecreasing imaginary part -/

/-- Any solution of the reverse flow, shifted by `W`, has a derivative given by the genuine
(untruncated) vector field. This converts the integral equation in `IsReverseSol` into
differential form. -/
theorem isReverseSol_hasDerivWithinAt (W : ℝ → ℝ) (z : ℂ) (T : ℝ) {u : ℝ → ℂ}
    (h : IsReverseSol W z T u) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => u s + (W s : ℂ)) (-2 / u t) (Set.Icc (0 : ℝ) T) t := by
  obtain ⟨hcont, hprop⟩ := h
  have hune : ∀ s ∈ Set.Icc (0 : ℝ) T, u s ≠ 0 := by
    intro s hs h0
    have him := (hprop s hs).1
    rw [h0] at him; simp at him
  have hgcont : ContinuousOn (fun s => (-2 : ℂ) / u s) (Set.Icc (0 : ℝ) T) :=
    ContinuousOn.div continuousOn_const hcont hune
  have : Fact (t ∈ Set.Icc (0 : ℝ) T) := ⟨ht⟩
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := by
    rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc_right ht.2
  have hint : IntervalIntegrable (fun s => (-2 : ℂ) / u s) MeasureTheory.volume 0 t :=
    (hgcont.mono hsub).intervalIntegrable
  have hderiv0 : HasDerivWithinAt (fun r => ∫ x in (0 : ℝ)..r, (-2 : ℂ) / u x) (-2 / u t)
      (Set.Icc (0 : ℝ) T) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (hgcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hgcont t ht)
  have hderiv := hderiv0.const_add z
  have heq : ∀ s ∈ Set.Icc (0 : ℝ) T, u s + (W s : ℂ) = z + ∫ x in (0 : ℝ)..s, (-2 : ℂ) / u x := by
    intro s hs
    have hus := (hprop s hs).2
    have hnegdistrib : (∫ x in (0 : ℝ)..s, (-2 : ℂ) / u x) = -∫ x in (0 : ℝ)..s, (2 : ℂ) / u x := by
      have hpteq : ∀ x, (-2 : ℂ) / u x = -(2 / u x) := fun x => by ring
      simp_rw [hpteq]
      exact intervalIntegral.integral_neg
    rw [hnegdistrib, hus]
    ring
  exact hderiv.congr_of_mem heq ht

/-- Any solution of the reverse flow has nondecreasing imaginary part: this is the basic
monotonicity underlying the whole file, coming from `Im(-2/u) = 2 Im(u)/|u|² ≥ 0`. -/
theorem isReverseSol_monotoneOn_im (W : ℝ → ℝ) (z : ℂ) (T : ℝ) {u : ℝ → ℂ}
    (h : IsReverseSol W z T u) : MonotoneOn (fun t => (u t).im) (Set.Icc (0 : ℝ) T) := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => u s + (W s : ℂ)) (-2 / u t) (Set.Icc (0 : ℝ) T) t :=
    fun t ht => isReverseSol_hasDerivWithinAt W z T h ht
  have hcont : ContinuousOn (fun t => (u t).im) (Set.Icc (0 : ℝ) T) := by
    have huW : ContinuousOn (fun t => u t + (W t : ℂ)) (Set.Icc (0 : ℝ) T) :=
      fun t ht => (hderiv t ht).continuousWithinAt
    have h2 : ContinuousOn (fun t => (u t + (W t : ℂ)).im) (Set.Icc (0 : ℝ) T) :=
      Complex.continuous_im.comp_continuousOn huW
    have heq : ∀ t, (u t + (W t : ℂ)).im = (u t).im := by intro t; simp
    exact h2.congr (fun t _ => (heq t).symm)
  have hderivim : ∀ t ∈ interior (Set.Icc (0 : ℝ) T),
      HasDerivWithinAt (fun s => (u s).im) (-2 / u t).im (interior (Set.Icc (0 : ℝ) T)) t := by
    rw [interior_Icc]
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self ht
    have hd : HasDerivWithinAt (fun s => u s + (W s : ℂ)) (-2 / u t) (Set.Ioo (0 : ℝ) T) t :=
      (hderiv t ht').mono Set.Ioo_subset_Icc_self
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
    have hval : Complex.imCLM (-2 / u t) = (-2 / u t).im := Complex.imCLM_apply _
    have hfun : (Complex.imCLM ∘ fun s => u s + (W s : ℂ)) = fun s => (u s).im := by
      funext s
      show Complex.imCLM (u s + (W s : ℂ)) = (u s).im
      rw [Complex.imCLM_apply]
      simp
    rw [hval, hfun] at hcomp
    exact hcomp
  have hnonneg : ∀ t ∈ interior (Set.Icc (0 : ℝ) T), 0 ≤ (-2 / u t).im := by
    intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self ht
    obtain ⟨_, hprop0⟩ := h
    have him : 0 < (u t).im := (hprop0 t ht').1
    have hune : u t ≠ 0 := by intro h0; rw [h0] at him; simp at him
    have heqim : (-2 / u t).im = 2 * (u t).im / Complex.normSq (u t) := by
      have h1 : ((-2 : ℂ) * (u t)⁻¹).im = (-2) * (u t)⁻¹.im := by simp [Complex.mul_im]
      rw [show (-2 : ℂ) / u t = (-2 : ℂ) * (u t)⁻¹ from div_eq_mul_inv _ _, h1, Complex.inv_im]
      ring
    rw [heqim]
    exact div_nonneg (by linarith) (Complex.normSq_nonneg _)
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hcont hderivim hnonneg

/-! ### Restriction -/

theorem isReverseSol_restrict (W : ℝ → ℝ) (z : ℂ) {T t : ℝ} {u : ℝ → ℂ}
    (h : IsReverseSol W z T u) (_ht0 : 0 ≤ t) (htT : t ≤ T) : IsReverseSol W z t u := by
  obtain ⟨hcont, hprop⟩ := h
  refine ⟨hcont.mono (Set.Icc_subset_Icc_right htT), fun s hs => ?_⟩
  exact hprop s (Set.Icc_subset_Icc_right htT hs)

/-! ### Existence -/

theorem exists_isReverseSol (W : ℝ → ℝ) (hW : Continuous W) (z : ℂ) (hz : 0 < z.im) (T : ℝ)
    (hT : 0 ≤ T) : ∃ u : ℝ → ℂ, IsReverseSol W z T u := by
  set δ := z.im with hδdef
  have hδ : 0 < δ := hz
  have ht0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  set t₀ : ↥(Set.Icc (0 : ℝ) T) := ⟨0, ht0mem⟩ with ht0def
  have ht₀0 : (t₀ : ℝ) = 0 := rfl
  have hpl : IsPicardLindelof (fun t y => revVFTrunc W δ t y) t₀ z
      (⟨(2 / δ) * T, by positivity⟩ : ℝ≥0) 0 (⟨2 / δ, by positivity⟩ : ℝ≥0)
      (⟨4 / δ ^ 2, by positivity⟩ : ℝ≥0) := by
    refine ⟨fun t _ => (lipschitzWith_revVFTrunc W δ hδ t).lipschitzOnWith,
      fun y _ => (continuous_revVFTrunc W hW δ hδ y).continuousOn,
      fun t _ y _ => norm_revVFTrunc_le W δ hδ t y, ?_⟩
    show (2 / δ) * max (T - 0) (0 - 0) ≤ (2 / δ) * T - 0
    have hmax : max (T - 0) ((0 : ℝ) - 0) = T := by rw [sub_zero, sub_zero]; exact max_eq_left hT
    rw [hmax]; linarith
  obtain ⟨α, hα0, hαderiv⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0' : α 0 = z := by rw [← ht₀0]; exact hα0
  have hαcont : ContinuousOn α (Set.Icc (0 : ℝ) T) := fun t ht => (hαderiv t ht).continuousWithinAt
  have hαimcont : ContinuousOn (fun t => (α t).im) (Set.Icc (0 : ℝ) T) :=
    Complex.continuous_im.comp_continuousOn hαcont
  have hderivim : ∀ t ∈ interior (Set.Icc (0 : ℝ) T),
      HasDerivWithinAt (fun s => (α s).im) (revVFTrunc W δ t (α t)).im
        (interior (Set.Icc (0 : ℝ) T)) t := by
    rw [interior_Icc]
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self ht
    have hd : HasDerivWithinAt α (revVFTrunc W δ t (α t)) (Set.Ioo (0 : ℝ) T) t :=
      (hαderiv t ht').mono Set.Ioo_subset_Icc_self
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
    have hval : Complex.imCLM (revVFTrunc W δ t (α t)) = (revVFTrunc W δ t (α t)).im :=
      Complex.imCLM_apply _
    have hfun : (Complex.imCLM ∘ α) = fun s => (α s).im := by
      funext s; exact Complex.imCLM_apply (α s)
    rw [hval, hfun] at hcomp
    exact hcomp
  have hnonneg : ∀ t ∈ interior (Set.Icc (0 : ℝ) T), 0 ≤ (revVFTrunc W δ t (α t)).im :=
    fun t _ => im_revVFTrunc_nonneg W δ hδ t (α t)
  have hmono : MonotoneOn (fun t => (α t).im) (Set.Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hαimcont hderivim hnonneg
  have hge : ∀ t ∈ Set.Icc (0 : ℝ) T, δ ≤ (α t).im := by
    intro t ht
    have h1 := hmono (Set.left_mem_Icc.mpr hT) ht ht.1
    simpa [hα0'] using h1
  have hclamp_inactive : ∀ t ∈ Set.Icc (0 : ℝ) T, clampIm δ (α t) = α t := by
    intro t ht
    have h1 := hge t ht
    apply Complex.ext
    · exact clampIm_re δ (α t)
    · rw [clampIm_im]; exact max_eq_left h1
  set u : ℝ → ℂ := fun t => α t - (W t : ℂ) with hudef
  have huim : ∀ t, (u t).im = (α t).im := by intro t; simp [hudef]
  have hucont : ContinuousOn u (Set.Icc (0 : ℝ) T) :=
    hαcont.sub (Complex.continuous_ofReal.comp hW).continuousOn
  have hune : ∀ s ∈ Set.Icc (0 : ℝ) T, u s ≠ 0 := by
    intro s hs h0
    have h1 : δ ≤ (u s).im := by rw [huim]; exact hge s hs
    rw [h0] at h1; simp at h1; linarith
  have hderiv_all : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt α (-2 / u s) (Set.Icc (0 : ℝ) T) s := by
    intro s hs
    have hd := hαderiv s hs
    rw [revVFTrunc, hclamp_inactive s hs] at hd
    have hfe : (-2 : ℂ) / (α s - (W s : ℂ)) = -2 / u s := by rw [hudef]
    rwa [hfe] at hd
  refine ⟨u, hucont, fun t ht => ⟨?_, ?_⟩⟩
  · rw [huim]; exact lt_of_lt_of_le hδ (hge t ht)
  · have hlocal : ∀ s ∈ Set.Ioo (0 : ℝ) t, HasDerivWithinAt α (-2 / u s) (Set.Ioi s) s := by
      intro s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc_right ht.2 (Set.Ioo_subset_Icc_self hs)
      have hd : HasDerivWithinAt α (-2 / u s) (Set.Icc (0 : ℝ) t) s :=
        (hderiv_all s hs').mono (Set.Icc_subset_Icc_right ht.2)
      exact hd.mono_of_mem_nhdsWithin (icc_mem_nhdsWithin_Ioi hs.1.le hs.2)
    have hucont' : ContinuousOn α (Set.Icc (0 : ℝ) t) :=
      hαcont.mono (Set.Icc_subset_Icc_right ht.2)
    have hint' : IntervalIntegrable (fun s => (-2 : ℂ) / u s) MeasureTheory.volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.1]
      exact ContinuousOn.div continuousOn_const (hucont.mono (Set.Icc_subset_Icc_right ht.2))
        (fun s hs => hune s (Set.Icc_subset_Icc_right ht.2 hs))
    have hFTC : ∫ x in (0 : ℝ)..t, (-2 : ℂ) / u x = α t - α 0 :=
      integral_eq_sub_of_hasDeriv_right_of_le ht.1 hucont' hlocal hint'
    have hpteq : ∀ x, (-2 : ℂ) / u x = -(2 / u x) := fun x => by ring
    have hnegdistrib : (∫ x in (0 : ℝ)..t, (-2 : ℂ) / u x) = -∫ x in (0 : ℝ)..t, (2 : ℂ) / u x := by
      simp_rw [hpteq]; exact intervalIntegral.integral_neg
    have halpha : α t = z - ∫ x in (0 : ℝ)..t, (2 : ℂ) / u x := by
      have h1 : α t = α 0 + ∫ x in (0 : ℝ)..t, (-2 : ℂ) / u x := by rw [hFTC]; ring
      rw [h1, hnegdistrib, hα0']; ring
    show u t = z - (W t : ℂ) - ∫ x in (0 : ℝ)..t, 2 / u x
    rw [hudef]
    show α t - (W t : ℂ) = z - (W t : ℂ) - ∫ x in (0 : ℝ)..t, 2 / u x
    rw [halpha]
    ring

/-! ### Uniqueness -/

theorem isReverseSol_unique (W : ℝ → ℝ) (hW : Continuous W) (z : ℂ) (T : ℝ) (hT : 0 ≤ T)
    {u₁ u₂ : ℝ → ℂ} (h₁ : IsReverseSol W z T u₁) (h₂ : IsReverseSol W z T u₂) :
    Set.EqOn u₁ u₂ (Set.Icc 0 T) := by
  obtain ⟨hc1, hp1⟩ := h₁
  obtain ⟨hc2, hp2⟩ := h₂
  have hmono1 := isReverseSol_monotoneOn_im W z T ⟨hc1, hp1⟩
  have hmono2 := isReverseSol_monotoneOn_im W z T ⟨hc2, hp2⟩
  have hu10 : (u₁ 0).im = z.im := by
    have he := (hp1 0 ⟨le_refl 0, hT⟩).2; rw [he]; simp
  have hu20 : (u₂ 0).im = z.im := by
    have he := (hp2 0 ⟨le_refl 0, hT⟩).2; rw [he]; simp
  have hge1 : ∀ s ∈ Set.Icc (0 : ℝ) T, z.im ≤ (u₁ s).im := by
    intro s hs
    have h1 := hmono1 (Set.left_mem_Icc.mpr hT) hs hs.1
    simpa [hu10] using h1
  have hge2 : ∀ s ∈ Set.Icc (0 : ℝ) T, z.im ≤ (u₂ s).im := by
    intro s hs
    have h1 := hmono2 (Set.left_mem_Icc.mpr hT) hs hs.1
    simpa [hu20] using h1
  have hz : 0 < z.im := by
    have hpos := (hp1 0 ⟨le_refl 0, hT⟩).1
    rwa [hu10] at hpos
  set v₁ : ℝ → ℂ := fun t => u₁ t + (W t : ℂ) with hv1def
  set v₂ : ℝ → ℂ := fun t => u₂ t + (W t : ℂ) with hv2def
  have hv1cont : ContinuousOn v₁ (Set.Icc (0 : ℝ) T) :=
    hc1.add (Complex.continuous_ofReal.comp hW).continuousOn
  have hv2cont : ContinuousOn v₂ (Set.Icc (0 : ℝ) T) :=
    hc2.add (Complex.continuous_ofReal.comp hW).continuousOn
  have hderiv1 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt v₁ ((-2 : ℂ) / (v₁ t - (W t : ℂ))) (Set.Icc (0 : ℝ) T) t := by
    intro t ht
    have heq : v₁ t - (W t : ℂ) = u₁ t := by simp [hv1def]
    rw [heq]
    exact isReverseSol_hasDerivWithinAt W z T ⟨hc1, hp1⟩ ht
  have hderiv2 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt v₂ ((-2 : ℂ) / (v₂ t - (W t : ℂ))) (Set.Icc (0 : ℝ) T) t := by
    intro t ht
    have heq : v₂ t - (W t : ℂ) = u₂ t := by simp [hv2def]
    rw [heq]
    exact isReverseSol_hasDerivWithinAt W z T ⟨hc2, hp2⟩ ht
  have hloc1 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt v₁ ((-2 : ℂ) / (v₁ t - (W t : ℂ))) (Set.Ici t) t := fun t ht =>
    (hderiv1 t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (icc_mem_nhdsWithin_Ici ht.1 ht.2)
  have hloc2 : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt v₂ ((-2 : ℂ) / (v₂ t - (W t : ℂ))) (Set.Ici t) t := fun t ht =>
    (hderiv2 t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (icc_mem_nhdsWithin_Ici ht.1 ht.2)
  set s : ℝ → Set ℂ := fun _ => {y : ℂ | z.im ≤ y.im} with hsdef
  have hv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      LipschitzOnWith (⟨2 / z.im ^ 2, by positivity⟩ : ℝ≥0)
        (fun y => (-2 : ℂ) / (y - (W t : ℂ))) (s t) := by
    intro t _
    apply LipschitzOnWith.of_dist_le_mul
    intro y₁ hy₁ y₂ hy₂
    show dist ((-2 : ℂ) / (y₁ - (W t : ℂ))) ((-2 : ℂ) / (y₂ - (W t : ℂ)))
        ≤ (2 / z.im ^ 2) * dist y₁ y₂
    simp only [hsdef, Set.mem_setOf_eq] at hy₁ hy₂
    rw [dist_eq_norm, dist_eq_norm]
    have him1 : (y₁ - (W t : ℂ)).im = y₁.im := by simp
    have him2 : (y₂ - (W t : ℂ)).im = y₂.im := by simp
    have hw1 : z.im ≤ ‖y₁ - (W t : ℂ)‖ := by
      have h0 := Complex.im_le_norm (y₁ - (W t : ℂ)); rw [him1] at h0; linarith
    have hw2 : z.im ≤ ‖y₂ - (W t : ℂ)‖ := by
      have h0 := Complex.im_le_norm (y₂ - (W t : ℂ)); rw [him2] at h0; linarith
    have hw10 : y₁ - (W t : ℂ) ≠ 0 := by intro h; rw [h, norm_zero] at hw1; linarith
    have hw20 : y₂ - (W t : ℂ) ≠ 0 := by intro h; rw [h, norm_zero] at hw2; linarith
    have hrw : (-2 : ℂ) / (y₁ - (W t : ℂ)) - (-2 : ℂ) / (y₂ - (W t : ℂ))
        = 2 * (y₁ - y₂) / ((y₁ - (W t : ℂ)) * (y₂ - (W t : ℂ))) := by
      field_simp
      ring
    have hprod : z.im ^ 2 ≤ ‖y₁ - (W t : ℂ)‖ * ‖y₂ - (W t : ℂ)‖ := by
      have hm := mul_le_mul hw1 hw2 hz.le (hz.le.trans hw1)
      nlinarith [hm]
    have step1 : 2 * ‖y₁ - y₂‖ * z.im ^ 2 ≤ 2 * ‖y₁ - y₂‖ * (‖y₁ - (W t : ℂ)‖ * ‖y₂ - (W t : ℂ)‖) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    rw [hrw, norm_div, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num,
      div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [step1]
  have hfs1 : ∀ t ∈ Set.Ico (0 : ℝ) T, v₁ t ∈ s t := by
    intro t ht
    show z.im ≤ (v₁ t).im
    have h1 : (u₁ t).im ≤ (v₁ t).im := by
      have : (v₁ t).im = (u₁ t).im := by simp [hv1def]
      rw [this]
    exact le_trans (hge1 t (Set.Ico_subset_Icc_self ht)) h1
  have hfs2 : ∀ t ∈ Set.Ico (0 : ℝ) T, v₂ t ∈ s t := by
    intro t ht
    show z.im ≤ (v₂ t).im
    have h1 : (u₂ t).im ≤ (v₂ t).im := by
      have : (v₂ t).im = (u₂ t).im := by simp [hv2def]
      rw [this]
    exact le_trans (hge2 t (Set.Ico_subset_Icc_self ht)) h1
  have key : Set.EqOn v₁ v₂ (Set.Icc 0 T) := by
    apply ODE_solution_unique_of_mem_Icc_right hv hv1cont hloc1 hfs1 hv2cont hloc2 hfs2
    show v₁ 0 = v₂ 0
    show u₁ 0 + (W 0 : ℂ) = u₂ 0 + (W 0 : ℂ)
    have e1 := (hp1 0 ⟨le_refl 0, hT⟩).2
    have e2 := (hp2 0 ⟨le_refl 0, hT⟩).2
    rw [e1, e2, intervalIntegral.integral_same, intervalIntegral.integral_same]
  intro t ht
  have hkey := key ht
  have h1 : v₁ t = v₂ t := hkey
  simp only [hv1def, hv2def] at h1
  exact add_right_cancel h1

/-! ### `revMap` computes the unique solution -/

theorem revMap_eq (W : ℝ → ℝ) (hW : Continuous W) (z : ℂ) {T t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {u : ℝ → ℂ} (h : IsReverseSol W z T u) : revMap W t z = u t := by
  classical
  have hres : IsReverseSol W z t u := isReverseSol_restrict W z h ht0 htT
  have hex : ∃ u', IsReverseSol W z t u' := ⟨u, hres⟩
  show (if h : ∃ u', IsReverseSol W z t u' then (Classical.choose h) t else 0) = u t
  rw [dif_pos hex]
  have huniq := isReverseSol_unique W hW z t ht0 (Classical.choose_spec hex) hres
  exact huniq ⟨ht0, le_refl t⟩

/-! ### The flow only moves up -/

theorem im_le_im_revMap (W : ℝ → ℝ) (hW : Continuous W) (z : ℂ) (hz : 0 < z.im) {t : ℝ}
    (ht : 0 ≤ t) : z.im ≤ (revMap W t z).im := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz t ht
  rw [revMap_eq W hW z ht (le_refl t) hu]
  have hmono := isReverseSol_monotoneOn_im W z t hu
  have h0 : (u 0).im = z.im := by
    have he := hu.2 0 ⟨le_refl 0, ht⟩
    have := he.2; rw [this]; simp
  have hge := hmono (Set.left_mem_Icc.mpr ht) ⟨ht, le_refl t⟩ ht
  simpa [h0] using hge

/-! ### Quantitative bound on the displacement of the flow -/

theorem norm_revMap_sub_le (W : ℝ → ℝ) (hW : Continuous W) (z : ℂ) (hz : 0 < z.im) {t : ℝ}
    (ht : 0 ≤ t) : ‖revMap W t z - (z - (W t : ℂ))‖ ≤ 2 * t / z.im := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz t ht
  rw [revMap_eq W hW z ht (le_refl t) hu]
  obtain ⟨hucont, hprop⟩ := hu
  have heq : u t - (z - (W t : ℂ)) = -∫ s in (0 : ℝ)..t, (2 : ℂ) / u s := by
    have := (hprop t ⟨ht, le_refl t⟩).2
    rw [this]; ring
  rw [heq, norm_neg]
  have hmono := isReverseSol_monotoneOn_im W z t ⟨hucont, hprop⟩
  have h0 : (u 0).im = z.im := by
    have := (hprop 0 ⟨le_refl 0, ht⟩).2
    rw [this]; simp
  have hge : ∀ s ∈ Set.Icc (0 : ℝ) t, z.im ≤ (u s).im := by
    intro s hs
    have h1 := hmono (Set.left_mem_Icc.mpr ht) hs hs.1
    simpa [h0] using h1
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖(2 : ℂ) / u s‖ ≤ 2 / z.im := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) t := by
      rw [Set.uIoc_of_le ht] at hs
      exact Set.Ioc_subset_Icc_self hs
    have h1 : z.im ≤ ‖u s‖ := le_trans (hge s hs') (Complex.im_le_norm _)
    have h1' : 0 < ‖u s‖ := lt_of_lt_of_le hz h1
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 from by norm_num, div_le_div_iff₀ h1' hz]
    nlinarith [h1]
  calc ‖∫ s in (0 : ℝ)..t, (2 : ℂ) / u s‖ ≤ (2 / z.im) * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = 2 * t / z.im := by rw [sub_zero, abs_of_nonneg ht]; ring

end QuantumZipper
