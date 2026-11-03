/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistFTC at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ExistDist
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts against rectangle indicators (task P2-EXIST)

`integral_d12_mul_rectInd`: `∫ ∂_re ∂_im φ(x) · 1_{[0,x]}(u) dx = φ(u)` for `φ ∈ 𝓓(ℂ)`, i.e. the
antiderivative field `F(x) = ⟨h, 1_{[0,x]}⟩` satisfies `∫ F ∂_re ∂_im φ = ⟨h, φ⟩`. Proof: the
fundamental theorem of calculus on half-lines twice (mathlib
`integral_Ioi_of_hasDerivAt_of_tendsto`, `integral_Iic_of_hasDerivAt_of_tendsto`) and Fubini on
`ℂ ≅ ℝ × ℝ`. Own elementary proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology

namespace LQGMetric
namespace GFFExist

/-- one-dimensional step: `∫ f'(t) s(t, b) dt = −f(b)` for compactly supported `f`. -/
lemma integral_deriv_mul_sgnInd {f f' : ℝ → ℝ} (hd : ∀ t, HasDerivAt f (f' t) t)
    (hf'i : Integrable f') {L : ℝ} (hL : ∀ t, L < |t| → f t = 0) (b : ℝ) :
    ∫ t, f' t * sgnInd t b = -f b := by
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  rcases lt_or_ge 0 b with hb | hb
  · have e : (fun t => f' t * sgnInd t b) = (Ici b).indicator f' := by
      funext t
      rw [sgnInd_of_pos hb]
      by_cases ht : b ≤ t
      · rw [if_pos ht, indicator_of_mem (show t ∈ Ici b from ht), mul_one]
      · rw [if_neg ht, indicator_of_notMem (show t ∉ Ici b from ht), mul_zero]
    rw [e, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
    have htend : Tendsto f atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop |L|] with t ht
      exact (hL t (lt_of_le_of_lt (le_abs_self L) (ht.trans_le (le_abs_self t)))).symm
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
      (fun t _ => hd t) hf'i.integrableOn htend, zero_sub]
  · have e : (fun t => f' t * sgnInd t b) = fun t => -(Iio b).indicator f' t := by
      funext t
      rw [sgnInd_of_nonpos hb]
      by_cases ht : t < b
      · rw [if_pos ht, indicator_of_mem (show t ∈ Iio b from ht)]; ring
      · rw [if_neg ht, indicator_of_notMem (show t ∉ Iio b from ht)]; ring
    rw [e, integral_neg, integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio]
    have htend : Tendsto f atBot (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_lt_atBot (-|L|)] with t ht
      refine (hL t ?_).symm
      have : -t ≤ |t| := neg_le_abs t
      linarith [neg_abs_le L, le_abs_self L]
    rw [integral_Iic_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
      (fun t _ => hd t) hf'i.integrableOn htend, sub_zero]

/-- a test function vanishes outside some ball -/
lemma testC_exists_vanish (χ : TestC) : ∃ L, 0 ≤ L ∧ ∀ z : ℂ, L < ‖z‖ → χ z = 0 := by
  obtain ⟨L, hL⟩ := (χ.hasCompactSupport.isCompact.isBounded).subset_closedBall 0
  refine ⟨max L 0, le_max_right _ _, fun z hz => ?_⟩
  by_contra h
  have := hL (subset_tsupport _ h)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left L 0]

lemma testC_bounded (χ : TestC) : ∃ C, ∀ z : ℂ, |χ z| ≤ C := by
  obtain ⟨C, hC⟩ := (χ.continuous.norm.bddAbove_range_of_hasCompactSupport
    χ.hasCompactSupport.norm)
  exact ⟨C, fun z => by simpa [Real.norm_eq_abs] using hC ⟨z, rfl⟩⟩

/-- slices `t ↦ χ(a + t b)`, `‖b‖ = 1`, vanish for `|t| > L + ‖a‖` -/
lemma testC_slice_vanish (χ : TestC) {L : ℝ} (hL : ∀ z : ℂ, L < ‖z‖ → χ z = 0) (a b : ℂ)
    (hb : ‖b‖ = 1) (t : ℝ) (ht : L + ‖a‖ < |t|) : χ (a + t * b) = 0 := by
  refine hL _ ?_
  have h1 : ‖(t : ℂ) * b‖ = |t| := by rw [norm_mul, hb, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(t : ℂ) * b‖ ≤ ‖a + t * b‖ + ‖a‖ := by
    calc ‖(t : ℂ) * b‖ = ‖(a + t * b) - a‖ := by ring_nf
      _ ≤ ‖a + t * b‖ + ‖a‖ := norm_sub_le _ _
  linarith

/-- slices of test functions are integrable -/
lemma testC_integrable_slice (χ : TestC) (a b : ℂ) (hb : ‖b‖ = 1) :
    Integrable fun t : ℝ => χ (a + t * b) := by
  have hc : Continuous fun t : ℝ => χ (a + t * b) := χ.continuous.comp (by fun_prop)
  obtain ⟨L, _, hL⟩ := testC_exists_vanish χ
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (isCompact_Icc (a := -(L + ‖a‖)) (b := L + ‖a‖)) fun t ht => ?_)
  refine testC_slice_vanish χ hL a b hb t ?_
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · have := neg_abs_le t; linarith
  · have := le_abs_self t; linarith

lemma measurable_sgnInd_left (b : ℝ) : Measurable fun a => sgnInd a b := by
  unfold sgnInd
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact (MeasurableSet.const (0 < b)).inter (measurableSet_le measurable_const measurable_id)
  · exact (measurableSet_lt measurable_id measurable_const).inter (MeasurableSet.const (b ≤ 0))

lemma hasDerivAt_testC_slice (χ : TestC) (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => χ (a + t * b)) (fderiv ℝ χ (a + t * b) b) t := by
  have hg : HasDerivAt (fun t : ℝ => a + (t : ℂ) * b) b t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const b).const_add a
  have hχ : DifferentiableAt ℝ χ (a + t * b) :=
    (χ.contDiff.differentiable (by simp)).differentiableAt
  exact hχ.hasFDerivAt.comp_hasDerivAt t hg

/-- `∂_im φ` as a test function -/
def dIm (φ : TestC) : TestC := (TestFunction.lineDerivCLM ℝ Complex.I : TestC →L[ℝ] TestC) φ

lemma dIm_apply (φ : TestC) (z : ℂ) : dIm φ z = fderiv ℝ φ z Complex.I := by
  rw [dIm, TestFunction.lineDerivCLM_apply_of_le le_top,
    ((φ.contDiff.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv]

lemma d12_apply (φ : TestC) (z : ℂ) : d12 φ z = fderiv ℝ (dIm φ) z 1 := by
  rw [d12, ContinuousLinearMap.comp_apply, TestFunction.lineDerivCLM_apply_of_le le_top]
  change lineDeriv ℝ (⇑(dIm φ)) z 1 = _
  rw [(((dIm φ).contDiff.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv]

/-- **Integration by parts against rectangles**: `∫ ∂_re ∂_im φ(x) 1_{[0,x]}(u) dx = φ(u)`. -/
theorem integral_d12_mul_rectInd (φ : TestC) (u : ℂ) :
    ∫ x, d12 φ x * rectInd x u = φ u := by
  have hint : Integrable fun x => d12 φ x * rectInd x u := by
    refine (GFFInv.integrable_test (d12 φ)).mono ((d12 φ).continuous.measurable.mul
      (((measurable_sgnInd_left _).comp Complex.measurable_re).mul
        ((measurable_sgnInd_left _).comp Complex.measurable_im))).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, rectInd, abs_mul]
    have h1 := abs_sgnInd_le_one x.re u.re
    have h2 := abs_sgnInd_le_one x.im u.im
    have h3 := abs_nonneg (d12 φ x)
    calc |d12 φ x| * (|sgnInd x.re u.re| * |sgnInd x.im u.im|) ≤ |d12 φ x| * (1 * 1) := by
          gcongr
      _ = _ := by ring
  rw [integral_complex_eq, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod_symm _ (integrable_complex_iff.1 hint)]
  obtain ⟨L, _, hL⟩ := testC_exists_vanish (dIm φ)
  obtain ⟨L', _, hL'⟩ := testC_exists_vanish φ
  have hinner : ∀ p2 : ℝ, ∫ p1 : ℝ, d12 φ ⟨p1, p2⟩ * rectInd ⟨p1, p2⟩ u =
      -(dIm φ ⟨u.re, p2⟩ * sgnInd p2 u.im) := by
    intro p2
    have e : ∀ p1 : ℝ, (⟨p1, p2⟩ : ℂ) = (p2 * Complex.I : ℂ) + (p1 : ℂ) * 1 := fun p1 => by
      apply Complex.ext <;> simp
    have h1 := integral_deriv_mul_sgnInd (f := fun t : ℝ => dIm φ ((p2 * Complex.I : ℂ) + t * 1))
      (f' := fun t => d12 φ ((p2 * Complex.I : ℂ) + t * 1))
      (fun t => by
        have := hasDerivAt_testC_slice (dIm φ) (p2 * Complex.I) 1 t
        rwa [← d12_apply] at this)
      (testC_integrable_slice (d12 φ) _ 1 (by simp))
      (L := L + ‖(p2 * Complex.I : ℂ)‖)
      (fun t ht => testC_slice_vanish (dIm φ) hL _ 1 (by simp) t ht) u.re
    have e2 : ((p2 * Complex.I : ℂ) + (u.re : ℂ) * 1) = ⟨u.re, p2⟩ := by
      apply Complex.ext <;> simp
    simp only [e2] at h1
    have e5 : ∀ p1 : ℝ, d12 φ ⟨p1, p2⟩ * rectInd ⟨p1, p2⟩ u =
        (d12 φ ((p2 * Complex.I : ℂ) + (p1 : ℂ) * 1) * sgnInd p1 u.re) * sgnInd p2 u.im := by
      intro p1
      rw [← e p1]
      simp only [rectInd]
      ring
    simp_rw [e5]
    rw [integral_mul_const, h1]
    ring
  simp only
  simp_rw [hinner]
  rw [integral_neg]
  have h2 := integral_deriv_mul_sgnInd (f := fun t : ℝ => φ ((u.re : ℂ) + t * Complex.I))
    (f' := fun t => dIm φ ((u.re : ℂ) + t * Complex.I))
    (fun t => by
      have := hasDerivAt_testC_slice φ (u.re : ℂ) Complex.I t
      rwa [← dIm_apply] at this)
    (testC_integrable_slice (dIm φ) _ Complex.I (by simp))
    (L := L' + ‖(u.re : ℂ)‖)
    (fun t ht => testC_slice_vanish φ hL' _ Complex.I (by simp) t ht) u.im
  have e6 : ((u.re : ℂ) + (u.im : ℂ) * Complex.I) = u := Complex.re_add_im u
  have e7 : ∀ p2 : ℝ, ((u.re : ℂ) + (p2 : ℂ) * Complex.I) = ⟨u.re, p2⟩ := fun p2 => by
    apply Complex.ext <;> simp
  simp only [e6, e7] at h2
  rw [h2, neg_neg]

end GFFExist
end LQGMetric
