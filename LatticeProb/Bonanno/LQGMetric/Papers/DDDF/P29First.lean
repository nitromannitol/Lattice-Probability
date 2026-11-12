/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P29First at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Third
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareL1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Prop 29, first term: uniform bound for the kernel difference (task P2-DDDFP29, WP-110)

DDDF (arXiv:1904.08021), `tightness.tex:1566–1570`: for `x ∈ U`,
`Var(φ¹_t(x) − η¹_t(x)) = π ∫_0^{1−t} ∫_D (p_{t/2} * p^D_{s/2}(x,y) − p_{(t+s)/2}(x − y))² dy ds ≤ C'`
"using the kernel comparison (6.96)". The integral runs over `y ∈ D`, while (6.96) holds only for
`y ∈ U` (`d(y, ∂D) ≥ d`). We close this gap (own argument): for `y` at distance `≥ d/2` from
`∂D` use (6.96) with `d/2` (`abs_integral_heat_sqDir_sub_le`); otherwise `|x − y| ≥ d/2`, and
`|p_{t/2} * p^D_{s/2}(x,y)|` is bounded by splitting `y'` near/far from `x` and the `L¹` bound
`lintegral_abs_sqDirKernel_le`. Result: `firstKer` is bounded uniformly in `t > 0`,
`s ∈ (0, 2]`, `y ∈ D` (`abs_firstKer_le`), hence the variance bound (`lintegral_firstTerm_var_le`).
-/

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal

namespace LQGMetric
namespace HeatSq

/-- DDDF's first-term kernel `p_{t/2} * p^D_{s/2}(x,y) − p_{(t+s)/2}(x − y)`. -/
def firstKer (a L t s : ℝ) (x y : ℂ) : ℝ := thirdKer a L t s x y - heatKernel ((t + s) / 2) x y

/-- A uniform bound for the far-from-boundary constant. -/
def hkConst (d : ℝ) : ℝ := 2 * (π * d ^ 2)⁻¹

lemma hkConst_nonneg (d : ℝ) : 0 ≤ hkConst d := by unfold hkConst; positivity

lemma integral_abs_sqDirKernel_le {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (y : ℂ) :
    Integrable (fun y' => sqDirKernel a L r y' y) (volume.restrict (sqOpen a L)) ∧
      ∫ y' in sqOpen a L, |sqDirKernel a L r y' y| ≤ 4 := by
  have hb' : ∫⁻ y' in sqOpen a L, ENNReal.ofReal |sqDirKernel a L r y' y| ≤ 4 := by
    simp_rw [sqDirKernel_symm hr hL _ y]; exact lintegral_abs_sqDirKernel_le (a := a) hr hL y
  have hm : Measurable (fun y' => sqDirKernel a L r y' y) := measurable_sqDirKernel_left hr hL y
  have hI : Integrable (fun y' => sqDirKernel a L r y' y) (volume.restrict (sqOpen a L)) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact hb'.trans_lt (by norm_num)
  refine ⟨hI, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    hI.abs.aestronglyMeasurable]
  have : ∫⁻ y' in sqOpen a L, ENNReal.ofReal |sqDirKernel a L r y' y| ≤ 4 := hb'
  calc (∫⁻ y' in sqOpen a L, ENNReal.ofReal |sqDirKernel a L r y' y|).toReal
      ≤ (4 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by norm_num) this
    _ = 4 := by norm_num

/-- Near/far splitting of the integrand when `|x − y| ≥ d/2`. -/
lemma abs_heat_mul_sqDir_le {a L t r d : ℝ} (ht : 0 < t) (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d)
    (hL : 0 < L) {x y y' : ℂ} (hxre : x.re ∈ Icc (a + d) (a + L - d))
    (hxim : x.im ∈ Icc (a + d) (a + L - d)) (hy : y ∈ sqOpen a L) (hxy : d / 2 ≤ ‖x - y‖) :
    |heatKernel t x y' * sqDirKernel a L r y' y| ≤
      hkConst (d / 4) * |sqDirKernel a L r y' y| +
        (4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 + 1) * hkConst (d / 4) *
          heatKernel t x y' := by
  have hd4 : 0 < d / 4 := by positivity
  have hK := imgConst_nonneg (d / 4) L
  have hp := heatKernel_nonneg t ht.le x y'
  rcases le_or_gt (d / 4) ‖y' - x‖ with hfar | hnear
  · -- far: `p_t(x, y') ≤ p_t(d/4, 0) ≤ hkConst (d/4)`
    have h1 : heatKernel t x y' ≤ hkConst (d / 4) := by
      rw [heatKernel_symm]
      exact (heatKernel_le_of_le_norm ht hd4.le hfar).trans (heatKernel_d_le_const ht hd4)
    rw [abs_mul, abs_of_nonneg hp]
    have := mul_le_mul_of_nonneg_right h1 (abs_nonneg (sqDirKernel a L r y' y))
    have h2 : 0 ≤ (4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 + 1) *
        hkConst (d / 4) * heatKernel t x y' := by
      have := hkConst_nonneg (d / 4); positivity
    linarith
  · -- near: `y'` is interior and `|y' − y| ≥ d/4`
    have hre : |y'.re - x.re| < d / 4 := by
      have := Complex.abs_re_le_norm (y' - x); simp only [Complex.sub_re] at this; linarith
    have him : |y'.im - x.im| < d / 4 := by
      have := Complex.abs_im_le_norm (y' - x); simp only [Complex.sub_im] at this; linarith
    rw [abs_lt] at hre him
    have hy're : y'.re ∈ Icc (a + d / 4) (a + L - d / 4) :=
      ⟨by linarith [hxre.1], by linarith [hxre.2]⟩
    have hy'im : y'.im ∈ Icc (a + d / 4) (a + L - d / 4) :=
      ⟨by linarith [hxim.1], by linarith [hxim.2]⟩
    have hyy' : d / 4 ≤ ‖y - y'‖ := by
      have h1 := norm_sub_le_norm_sub_add_norm_sub x y' y
      rw [norm_sub_rev x y', norm_sub_rev y' y] at h1
      linarith
    have hhk : heatKernel r (d / 4 : ℝ) 0 ≤ hkConst (d / 4) := heatKernel_d_le_const hr hd4
    have hq := abs_sqDirKernel_sub_le hr hr1 hd4 hL (y' := y) (y := y') ⟨hy.1.le, hy.2.1.le⟩
      ⟨hy.2.2.1.le, hy.2.2.2.le⟩ hy're hy'im
    have hpy : heatKernel r y y' ≤ heatKernel r (d / 4 : ℝ) 0 := heatKernel_le_of_le_norm hr hd4.le hyy'
    have hpy0 := heatKernel_nonneg r hr.le y y'
    have hbD : |sqDirKernel a L r y' y| ≤
        (4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 + 1) * hkConst (d / 4) := by
      rw [sqDirKernel_symm hr hL]
      have := abs_sub_abs_le_abs_sub (sqDirKernel a L r y y') (heatKernel r y y')
      rw [abs_of_nonneg hpy0] at this
      have hk0 : 0 ≤ 4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hhk hk0]
    rw [abs_mul, abs_of_nonneg hp]
    have := mul_le_mul_of_nonneg_left hbD hp
    have h0 : 0 ≤ hkConst (d / 4) * |sqDirKernel a L r y' y| :=
      mul_nonneg (hkConst_nonneg _) (abs_nonneg _)
    nlinarith

/-- The uniform bound for `firstKer`. -/
def firstConst (d L : ℝ) : ℝ :=
  (4 * imgConst (d / 2) L + 4 * imgConst (d / 2) L ^ 2 + 1) * hkConst (d / 2) +
    (4 * hkConst (d / 4) + (4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 + 1) *
      hkConst (d / 4)) + hkConst (d / 2)

/-- **Uniform bound for the first-term kernel** (fixing the use of (6.96) near `∂D`,
`tightness.tex:1568`): for `t > 0`, `0 < s ≤ 2`, `x ∈ [a+d, a+L−d]²`, `y ∈ D`,
`|p_{t/2} * p^D_{s/2}(x,y) − p_{(t+s)/2}(x,y)| ≤ C(d, L)`. -/
theorem abs_firstKer_le {a L t s d : ℝ} (ht : 0 < t) (hs : 0 < s) (hs2 : s ≤ 2) (hd : 0 < d)
    (hL : 0 < L) {x y : ℂ} (hxre : x.re ∈ Icc (a + d) (a + L - d))
    (hxim : x.im ∈ Icc (a + d) (a + L - d)) (hy : y ∈ sqOpen a L) :
    |firstKer a L t s x y| ≤ firstConst d L := by
  have hd2 : 0 < d / 2 := by positivity
  have hd4 : 0 < d / 4 := by positivity
  have hK2 := imgConst_nonneg (d / 2) L
  have hK4 := imgConst_nonneg (d / 4) L
  have hc2 := hkConst_nonneg (d / 2)
  have hc4 := hkConst_nonneg (d / 4)
  have hA0 : 0 ≤ (4 * imgConst (d / 2) L + 4 * imgConst (d / 2) L ^ 2 + 1) * hkConst (d / 2) := by
    positivity
  have hB0 : 0 ≤ 4 * hkConst (d / 4) + (4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 + 1) *
      hkConst (d / 4) := by positivity
  unfold firstKer thirdKer firstConst
  rw [show (t + s) / 2 = t / 2 + s / 2 by ring]
  by_cases hin : y.re ∈ Icc (a + d / 2) (a + L - d / 2) ∧ y.im ∈ Icc (a + d / 2) (a + L - d / 2)
  · have h := abs_integral_heat_sqDir_sub_le (a := a) (L := L) (half_pos ht) (half_pos hs)
      (by linarith) hd2 hL x y hin.1 hin.2
    have h2 : heatKernel (s / 2) (d / 2 : ℝ) 0 ≤ hkConst (d / 2) :=
      heatKernel_d_le_const (half_pos hs) hd2
    have := mul_le_mul_of_nonneg_left h2 (by positivity :
      (0 : ℝ) ≤ 4 * imgConst (d / 2) L + 4 * imgConst (d / 2) L ^ 2 + 1)
    linarith
  · -- `y` is within `d/2` of `∂D`, hence `|x − y| ≥ d/2`
    have hxy : d / 2 ≤ ‖x - y‖ := by
      have hre := Complex.abs_re_le_norm (x - y)
      have him := Complex.abs_im_le_norm (x - y)
      simp only [Complex.sub_re, Complex.sub_im] at hre him
      simp only [mem_Icc, not_and_or, not_le] at hin
      rcases hin with (h | h) | (h | h)
      · linarith [le_abs_self (x.re - y.re), hxre.1]
      · linarith [neg_abs_le (x.re - y.re), hxre.2]
      · linarith [le_abs_self (x.im - y.im), hxim.1]
      · linarith [neg_abs_le (x.im - y.im), hxim.2]
    obtain ⟨hI, hI4⟩ := integral_abs_sqDirKernel_le (a := a) (half_pos hs) hL y
    have hp := integrable_heatKernel (t / 2) (half_pos ht) x
    have hg : Integrable (fun y' => hkConst (d / 4) * |sqDirKernel a L (s / 2) y' y| +
        (4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 + 1) * hkConst (d / 4) *
          heatKernel (t / 2) x y') (volume.restrict (sqOpen a L)) :=
      (hI.abs.const_mul _).add (hp.restrict.const_mul _)
    have hb := norm_integral_le_of_norm_le hg ((ae_restrict_iff' (measurableSet_sqOpen a L)).mpr
      (Filter.Eventually.of_forall fun y' _ => by
        rw [Real.norm_eq_abs]
        exact abs_heat_mul_sqDir_le (half_pos ht) (half_pos hs) (by linarith) hd hL hxre hxim
          hy hxy))
    rw [Real.norm_eq_abs, integral_add (hI.abs.const_mul _) (hp.restrict.const_mul _),
      integral_const_mul, integral_const_mul] at hb
    have hp1 : ∫ y' in sqOpen a L, heatKernel (t / 2) x y' ≤ 1 := by
      rw [← integral_heatKernel (t / 2) (half_pos ht) x]
      exact setIntegral_le_integral hp (Filter.Eventually.of_forall
        (heatKernel_nonneg (t / 2) (half_pos ht).le x))
    have hb' : |∫ y' in sqOpen a L, heatKernel (t / 2) x y' * sqDirKernel a L (s / 2) y' y| ≤
        4 * hkConst (d / 4) + (4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 + 1) *
          hkConst (d / 4) := by
      refine hb.trans ?_
      have hC : 0 ≤ (4 * imgConst (d / 4) L + 4 * imgConst (d / 4) L ^ 2 + 1) * hkConst (d / 4) :=
        by positivity
      nlinarith [mul_le_mul_of_nonneg_left hI4 hc4, mul_le_mul_of_nonneg_left hp1 hC]
    have hpxy : heatKernel (t / 2 + s / 2) x y ≤ hkConst (d / 2) := by
      rw [heatKernel_symm]
      exact (heatKernel_le_of_le_norm (by positivity) hd2.le (by rwa [norm_sub_rev])).trans
        (heatKernel_d_le_const (by positivity) hd2)
    have hp0 := heatKernel_nonneg (t / 2 + s / 2) (by positivity) x y
    have := abs_sub (∫ y' in sqOpen a L, heatKernel (t / 2) x y' * sqDirKernel a L (s / 2) y' y)
      (heatKernel (t / 2 + s / 2) x y)
    rw [abs_of_nonneg hp0] at this
    linarith

/-- **First term, variance** (DDDF `tightness.tex:1566–1570`): uniformly in `t > 0`,
`∫_0^2 ∫_D (p_{t/2} * p^D_{s/2}(x,y) − p_{(t+s)/2}(x,y))² dy ds ≤ 2 C(d,L)² L²`. -/
theorem lintegral_firstTerm_var_le {a L t d : ℝ} (ht : 0 < t) (hd : 0 < d) (hL : 0 < L)
    {x : ℂ} (hxre : x.re ∈ Icc (a + d) (a + L - d)) (hxim : x.im ∈ Icc (a + d) (a + L - d)) :
    ∫⁻ s in Ioc 0 2, ∫⁻ y in sqOpen a L, ENNReal.ofReal (firstKer a L t s x y ^ 2) ≤
      ENNReal.ofReal (firstConst d L ^ 2 * L ^ 2 * 2) := by
  have hpt : ∀ s ∈ Ioc (0 : ℝ) 2, ∫⁻ y in sqOpen a L, ENNReal.ofReal (firstKer a L t s x y ^ 2) ≤
      ENNReal.ofReal (firstConst d L ^ 2 * L ^ 2) := by
    intro s hs
    refine (setLIntegral_mono' (measurableSet_sqOpen a L) (fun y hy =>
      ENNReal.ofReal_le_ofReal (?_ : firstKer a L t s x y ^ 2 ≤ firstConst d L ^ 2))).trans_eq ?_
    · rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_firstKer_le ht hs.1 hs.2 hd hL hxre hxim hy) 2
    · rw [setLIntegral_const, volume_sqOpen a L hL.le, ← ENNReal.ofReal_mul (sq_nonneg _)]
  refine (setLIntegral_mono' measurableSet_Ioc hpt).trans_eq ?_
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]

end HeatSq
end LQGMetric
