/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareCK at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquare
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Chapman–Kolmogorov for the planar heat kernel; measurability and symmetry of the image kernel
(task P2-DDDFP29, WP-110)

* `HeatSq.integral_heatKernel_mul_heatKernel_ck`: `∫ p_t(x,y') p_s(y',y) dy' = p_{t+s}(x,y)`,
  the Chapman–Kolmogorov identity used in DDDF Prop 29 (`tightness.tex:1553`, "using
  Chapman-Kolmogorov"). Proof: completing the square and mathlib's Gaussian integral
  `GaussianFourier.integral_rexp_neg_mul_sq_norm`, generalizing the equal-time case
  `WhiteNoise.integral_heatKernel_mul_heatKernel` (own elementary proof of a standard fact).
* `HeatSq.measurable_intervalDirKernel`, `HeatSq.measurable_sqDirKernel`: joint measurability of
  the image-series kernels (as `toReal` of `ℝ≥0∞`-valued sums of continuous functions).
* `HeatSq.intervalDirKernel_symm`: `q_s(u,v) = q_s(v,u)`.
-/

noncomputable section

open MeasureTheory Real

namespace LQGMetric
namespace HeatSq

lemma sq_norm_complex (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- Completing the square for different times: with `β = (t+s)/(2ts)` and
`m = (s x + t y)/(t+s)`, `p_t(x,y') p_s(y',y) = (2πt)⁻¹(2πs)⁻¹ e^{−|x−y|²/(2(t+s))} e^{−β|y'−m|²}`. -/
lemma heatKernel_mul_heatKernel_ck (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x y' y : ℂ) :
    heatKernel t x y' * heatKernel s y' y =
      ((2 * π * t)⁻¹ * (2 * π * s)⁻¹ * Real.exp (-‖x - y‖ ^ 2 / (2 * (t + s)))) *
        Real.exp (-((t + s) / (2 * t * s)) *
          ‖y' - (((s / (t + s) : ℝ) : ℂ) * x + ((t / (t + s) : ℝ) : ℂ) * y)‖ ^ 2) := by
  have hts : 0 < t + s := by positivity
  have key : -‖x - y'‖ ^ 2 / (2 * t) + -‖y' - y‖ ^ 2 / (2 * s) =
      -‖x - y‖ ^ 2 / (2 * (t + s)) + -((t + s) / (2 * t * s)) *
        ‖y' - (((s / (t + s) : ℝ) : ℂ) * x + ((t / (t + s) : ℝ) : ℂ) * y)‖ ^ 2 := by
    simp only [sq_norm_complex, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    field_simp
    ring
  unfold heatKernel
  rw [mul_mul_mul_comm, ← Real.exp_add, key, Real.exp_add]
  ring

lemma integrable_heatKernel_mul_heatKernel_ck (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x y : ℂ) :
    Integrable (fun y' => heatKernel t x y' * heatKernel s y' y) := by
  have hb : 0 < (t + s) / (2 * t * s) := by positivity
  simp_rw [heatKernel_mul_heatKernel_ck t s ht hs x _ y]
  exact ((integrable_rexp_neg_mul_sq_norm_complex hb).comp_sub_right _).const_mul _

/-- **Chapman–Kolmogorov**: `∫ p_t(x,y') p_s(y',y) dy' = p_{t+s}(x,y)`. -/
theorem integral_heatKernel_mul_heatKernel_ck (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x y : ℂ) :
    ∫ y', heatKernel t x y' * heatKernel s y' y = heatKernel (t + s) x y := by
  have hb : 0 < (t + s) / (2 * t * s) := by positivity
  simp_rw [heatKernel_mul_heatKernel_ck t s ht hs x _ y]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y' : ℂ => Real.exp (-((t + s) / (2 * t * s)) * ‖y'‖ ^ 2)),
    GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  simp only [Complex.finrank_real_complex]
  norm_num
  unfold heatKernel
  have hts : 0 < t + s := by positivity
  field_simp

lemma continuous_gauss1 (s : ℝ) : Continuous (gauss1 s) := by
  unfold gauss1; fun_prop

/-- Measurability of a nonnegative image family `u ↦ ∑ₙ g_s(c(u) + 2nL)`. -/
lemma measurable_tsum_gauss1 {α : Type*} [MeasurableSpace α] (s L : ℝ) {c : α → ℝ}
    (hc : Measurable c) : Measurable (fun u => ∑' n : ℤ, gauss1 s (c u + 2 * n * L)) := by
  have e : (fun u => ∑' n : ℤ, gauss1 s (c u + 2 * n * L)) =
      fun u => (∑' n : ℤ, ENNReal.ofReal (gauss1 s (c u + 2 * n * L))).toReal := by
    funext u
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp [ENNReal.toReal_ofReal (gauss1_nonneg _ _)]
  rw [e]
  refine (Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp ?_).ennreal_toReal
  exact (continuous_gauss1 s).measurable.comp (hc.add_const _)

lemma intervalDirKernel_eq_sub {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (u v : ℝ) :
    intervalDirKernel a L s u v = ∑' n : ℤ, gauss1 s (u - v + 2 * n * L) -
      ∑' n : ℤ, gauss1 s (u + v - 2 * a + 2 * n * L) :=
  (summable_gauss1_shift hs hL _).tsum_sub (summable_gauss1_shift hs hL _)

/-- Joint measurability of the interval kernel along measurable arguments. -/
lemma measurable_intervalDirKernel {α : Type*} [MeasurableSpace α] {a L s : ℝ} (hs : 0 < s)
    (hL : 0 < L) {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => intervalDirKernel a L s (f p) (g p)) := by
  simp_rw [intervalDirKernel_eq_sub hs hL]
  exact (measurable_tsum_gauss1 s L (hf.sub hg)).sub
    (measurable_tsum_gauss1 s L ((hf.add hg).sub_const _))

/-- Joint measurability of the square kernel `(y', y) ↦ p^D_s(y', y)`. -/
lemma measurable_sqDirKernel {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) :
    Measurable (fun p : ℂ × ℂ => sqDirKernel a L s p.1 p.2) := by
  unfold sqDirKernel
  exact (measurable_intervalDirKernel hs hL (Complex.measurable_re.comp measurable_fst)
    (Complex.measurable_re.comp measurable_snd)).mul
    (measurable_intervalDirKernel hs hL (Complex.measurable_im.comp measurable_fst)
      (Complex.measurable_im.comp measurable_snd))

lemma gauss1_neg (s z : ℝ) : gauss1 s (-z) = gauss1 s z := by
  unfold gauss1; rw [neg_sq]

/-- **Symmetry** of the image kernel: `q_s(u,v) = q_s(v,u)`. -/
theorem intervalDirKernel_symm {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (u v : ℝ) :
    intervalDirKernel a L s u v = intervalDirKernel a L s v u := by
  rw [intervalDirKernel_eq_sub hs hL, intervalDirKernel_eq_sub hs hL]
  congr 1
  · rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; funext n
    rw [← gauss1_neg]; congr 1; simp; ring
  · congr 1; funext n; congr 1; ring

lemma sqDirKernel_symm {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (y' y : ℂ) :
    sqDirKernel a L s y' y = sqDirKernel a L s y y' := by
  unfold sqDirKernel
  rw [intervalDirKernel_symm hs hL y'.re, intervalDirKernel_symm hs hL y'.im]

end HeatSq
end LQGMetric
