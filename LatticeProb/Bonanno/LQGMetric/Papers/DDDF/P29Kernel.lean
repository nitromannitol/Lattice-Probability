/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P29Kernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Prop 29: the kernel comparison (6.96) on the square (task P2-DDDFP29, WP-110)

DDDF (arXiv:1904.08021), `tightness.tex:1547–1563`: for `y ∈ U`, `d = d(U, D^c)`,
`|p_{t/2} * p^D_{s/2}(x, y) − p_{(t+s)/2}(x − y)| ≤ C e^{−c/s}` uniformly in `t` (eq. (6.96),
label `eq:KernelComp`), where `p_{t/2} * p^D_{s/2}(x,y) = ∫_D p_{t/2}(x − y') p^D_{s/2}(y', y) dy'`.

DDDF's proof (`tightness.tex:1551–1559`): Chapman–Kolmogorov splits the difference into
`−∫_{D^c} p_{t/2}(x−y') p_{s/2}(y'−y) dy'` (small since `|y − y'| ≥ d`) and
`∫_D p_{t/2}(x−y') (p^D_{s/2} − p_{s/2})(y', y) dy'`, the latter bounded via Brownian bridges.
Here (D19, D-DDDF-11) `D = (a, a+L)²` and `p^D` is the image series `HeatSq.sqDirKernel`, so the
second term is bounded by `HeatSq.abs_sqDirKernel_sub_le` instead of the bridge estimate. We state
it for general times `t, s` (DDDF's `t/2, s/2`); the bound `C p_s(d, 0) = C (2πs)⁻¹ e^{−d²/(2s)}`
is DDDF's `C e^{−c/s}` (`heatKernel_d_le_exp`). The bound holds for every `x ∈ ℂ`.
-/

noncomputable section

open MeasureTheory Real Set

namespace LQGMetric
namespace HeatSq

/-- `p_s(y', y) ≤ p_s(d, 0)` when `‖y' − y‖ ≥ d ≥ 0`. -/
lemma heatKernel_le_of_le_norm {s d : ℝ} (hs : 0 < s) (hd : 0 ≤ d) {y' y : ℂ}
    (h : d ≤ ‖y' - y‖) : heatKernel s y' y ≤ heatKernel s (d : ℂ) 0 := by
  unfold heatKernel
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd, neg_div, neg_div,
    neg_le_neg_iff]
  gcongr

/-- Points outside the open square are at distance `≥ d` from `[a+d, a+L−d]²`. -/
lemma le_norm_of_not_mem_sqOpen {a L d : ℝ} {y' y : ℂ} (hy' : y' ∉ sqOpen a L)
    (hyre : y.re ∈ Icc (a + d) (a + L - d)) (hyim : y.im ∈ Icc (a + d) (a + L - d)) :
    d ≤ ‖y' - y‖ := by
  have hre : |(y' - y).re| ≤ ‖y' - y‖ := Complex.abs_re_le_norm _
  have him : |(y' - y).im| ≤ ‖y' - y‖ := Complex.abs_im_le_norm _
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  simp only [sqOpen, mem_setOf_eq, not_and_or, not_lt] at hy'
  rcases hy' with h | h | h | h
  · have := neg_abs_le (y'.re - y.re); linarith [hyre.1]
  · have := le_abs_self (y'.re - y.re); linarith [hyre.2]
  · have := neg_abs_le (y'.im - y.im); linarith [hyim.1]
  · have := le_abs_self (y'.im - y.im); linarith [hyim.2]

/-- **DDDF (6.96) on the square** (`tightness.tex:1561`): for `t > 0`, `0 < s ≤ 1`, any `x`
and `y ∈ [a+d, a+L−d]²`,
`|∫_D p_t(x,y') p^D_s(y',y) dy' − p_{t+s}(x,y)| ≤ (4K + 4K² + 1) p_s(d, 0)`. -/
theorem abs_integral_heat_sqDir_sub_le {a L t s d : ℝ} (ht : 0 < t) (hs : 0 < s) (hs1 : s ≤ 1)
    (hd : 0 < d) (hL : 0 < L) (x y : ℂ) (hyre : y.re ∈ Icc (a + d) (a + L - d))
    (hyim : y.im ∈ Icc (a + d) (a + L - d)) :
    |(∫ y' in sqOpen a L, heatKernel t x y' * sqDirKernel a L s y' y) - heatKernel (t + s) x y| ≤
      (4 * imgConst d L + 4 * imgConst d L ^ 2 + 1) * heatKernel s (d : ℂ) 0 := by
  set D := sqOpen a L
  have hD : MeasurableSet D := measurableSet_sqOpen a L
  set K := imgConst d L
  set B := (4 * K + 4 * K ^ 2) * heatKernel s (d : ℂ) 0
  set e := heatKernel s (d : ℂ) 0
  have he : 0 ≤ e := heatKernel_nonneg s hs.le _ _
  have hpt : Integrable (heatKernel t x) := integrable_heatKernel t ht x
  have hct : Continuous (heatKernel t x) := by unfold heatKernel; fun_prop
  have hcs : Continuous (fun y' => heatKernel s y' y) := by unfold heatKernel; fun_prop
  have hpt0 : ∀ y', 0 ≤ heatKernel t x y' := fun y' => heatKernel_nonneg t ht.le x y'
  have hpp : Integrable (fun y' => heatKernel t x y' * heatKernel s y' y) :=
    integrable_heatKernel_mul_heatKernel_ck t s ht hs x y
  -- the image part
  have hmemD : ∀ y' ∈ D, |sqDirKernel a L s y' y - heatKernel s y' y| ≤ B := fun y' hy' =>
    abs_sqDirKernel_sub_le hs hs1 hd hL ⟨hy'.1.le, hy'.2.1.le⟩ ⟨hy'.2.2.1.le, hy'.2.2.2.le⟩
      hyre hyim
  have hmeasq : Measurable (fun y' => sqDirKernel a L s y' y) := measurable_sqDirKernel_left hs hL y
  have hI1 : IntegrableOn (fun y' => heatKernel t x y' * (sqDirKernel a L s y' y -
      heatKernel s y' y)) D := by
    refine Integrable.mono' (hpt.restrict.mul_const B) ?_ ?_
    · exact (hct.measurable.mul (hmeasq.sub hcs.measurable)).aestronglyMeasurable
    · refine (ae_restrict_iff' hD).mpr (Filter.Eventually.of_forall fun y' hy' => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpt0 y')]
      exact mul_le_mul_of_nonneg_left (hmemD y' hy') (hpt0 y')
  have hsplit : ∫ y' in D, heatKernel t x y' * sqDirKernel a L s y' y =
      (∫ y' in D, heatKernel t x y' * (sqDirKernel a L s y' y - heatKernel s y' y)) +
        ∫ y' in D, heatKernel t x y' * heatKernel s y' y := by
    rw [← integral_add hI1 hpp.integrableOn]
    congr 1; funext y'; ring
  have hCK : heatKernel (t + s) x y = (∫ y' in D, heatKernel t x y' * heatKernel s y' y) +
      ∫ y' in Dᶜ, heatKernel t x y' * heatKernel s y' y := by
    rw [integral_add_compl hD hpp, integral_heatKernel_mul_heatKernel_ck t s ht hs x y]
  rw [hsplit, hCK, show ∀ p q r : ℝ, p + q - (q + r) = p - r by intros; ring]
  -- bounds on the two pieces
  have hb1 : |∫ y' in D, heatKernel t x y' * (sqDirKernel a L s y' y - heatKernel s y' y)| ≤ B := by
    have := norm_integral_le_of_norm_le (hpt.restrict.mul_const B) (f := fun y' =>
      heatKernel t x y' * (sqDirKernel a L s y' y - heatKernel s y' y)) ((ae_restrict_iff' hD).mpr
      (Filter.Eventually.of_forall fun y' hy' => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpt0 y')]
        exact mul_le_mul_of_nonneg_left (hmemD y' hy') (hpt0 y')))
    rw [Real.norm_eq_abs, integral_mul_const] at this
    refine this.trans ?_
    have h1 : ∫ y' in D, heatKernel t x y' ≤ 1 := by
      rw [← integral_heatKernel t ht x]
      exact setIntegral_le_integral hpt (Filter.Eventually.of_forall hpt0)
    have hB : 0 ≤ B := mul_nonneg (by have := imgConst_nonneg d L; positivity) he
    nlinarith
  have hb2 : |∫ y' in Dᶜ, heatKernel t x y' * heatKernel s y' y| ≤ e := by
    have hle : ∀ y' ∈ Dᶜ, heatKernel t x y' * heatKernel s y' y ≤ heatKernel t x y' * e :=
      fun y' hy' => mul_le_mul_of_nonneg_left (heatKernel_le_of_le_norm hs hd.le
        (le_norm_of_not_mem_sqOpen hy' hyre hyim)) (hpt0 y')
    have h0 : 0 ≤ ∫ y' in Dᶜ, heatKernel t x y' * heatKernel s y' y :=
      setIntegral_nonneg hD.compl fun y' _ =>
        mul_nonneg (hpt0 y') (heatKernel_nonneg s hs.le _ _)
    rw [abs_of_nonneg h0]
    refine (setIntegral_mono_on hpp.integrableOn (hpt.restrict.mul_const e) hD.compl hle).trans ?_
    rw [integral_mul_const]
    have h1 : ∫ y' in Dᶜ, heatKernel t x y' ≤ 1 := by
      rw [← integral_heatKernel t ht x]
      exact setIntegral_le_integral hpt (Filter.Eventually.of_forall hpt0)
    nlinarith
  calc _ ≤ |∫ y' in D, heatKernel t x y' * (sqDirKernel a L s y' y - heatKernel s y' y)| +
        |∫ y' in Dᶜ, heatKernel t x y' * heatKernel s y' y| := abs_sub _ _
    _ ≤ B + e := add_le_add hb1 hb2
    _ = _ := by simp only [B, e]; ring

/-- DDDF's form `C e^{−c/s}` of the bound: `p_s(d,0) ≤ 2 (π d²)⁻¹ e^{−d²/(4s)}`. -/
lemma heatKernel_d_le_exp {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    heatKernel s (d : ℂ) 0 ≤ 2 * (π * d ^ 2)⁻¹ * Real.exp (-(d ^ 2 / 4) / s) := by
  unfold heatKernel
  rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  -- `e^{−x} ≤ 1/x` with `x = d²/(4s)`
  set x := d ^ 2 / (4 * s)
  have hx : 0 < x := by positivity
  have hex : Real.exp (-x) * x ≤ 1 := by
    have := Real.add_one_le_exp x
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-x)]
  have e1 : -d ^ 2 / (2 * s) = -x + -(d ^ 2 / 4) / s := by simp only [x]; field_simp; ring
  rw [e1, Real.exp_add]
  have hpos := Real.exp_pos (-(d ^ 2 / 4) / s)
  have : (2 * π * s)⁻¹ * Real.exp (-x) ≤ 2 * (π * d ^ 2)⁻¹ := by
    rw [show 2 * (π * d ^ 2)⁻¹ = (2 * π * s)⁻¹ * (4 * s / d ^ 2) by field_simp; ring]
    have hxs : Real.exp (-x) ≤ 4 * s / d ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : x * (4 * s) = d ^ 2 := by simp only [x]; field_simp
      nlinarith
    have h2 : 0 < (2 * π * s)⁻¹ := by positivity
    nlinarith
  calc (2 * π * s)⁻¹ * (Real.exp (-x) * Real.exp (-(d ^ 2 / 4) / s))
      = ((2 * π * s)⁻¹ * Real.exp (-x)) * Real.exp (-(d ^ 2 / 4) / s) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right this hpos.le

end HeatSq
end LQGMetric
