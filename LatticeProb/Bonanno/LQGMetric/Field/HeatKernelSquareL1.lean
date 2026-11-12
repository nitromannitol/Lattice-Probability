/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareL1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
* `HeatSq.lintegral_abs_intervalDirKernel_le`: `∫_a^{a+L} |q_s(u,w)| dw ≤ 2`;
* `HeatSq.lintegral_abs_sqDirKernel_le`: `∫_D |p^D_s(x,y)| dy ≤ 4` on `D = (a,a+L)²`.

Both families of images of the Gaussian kernel fold onto `(a, a+L]` with total mass at most
`∫_ℝ g_s = 1` (`lintegral_fold`). These bounds control the first term of DDDF Prop 29 for
`y ∈ D` near `∂D`, where (6.96) is not available (`tightness.tex:1566–1570`). Own elementary
argument.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace HeatSq

lemma integral_gauss1_sub {s : ℝ} (hs : 0 < s) (u : ℝ) : ∫ w, gauss1 s (u - w) = 1 := by
  rw [integral_sub_left_eq_self (fun z => gauss1 s z) volume u]
  unfold gauss1
  rw [integral_const_mul]
  have e : (fun z : ℝ => Real.exp (-z ^ 2 / (2 * s))) = fun z => Real.exp (-(2 * s)⁻¹ * z ^ 2) := by
    funext z; congr 1; ring
  rw [e, integral_gaussian, show π / (2 * s)⁻¹ = 2 * π * s by field_simp]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne'

lemma lintegral_ofReal_gauss1_sub {s : ℝ} (hs : 0 < s) (u : ℝ) :
    ∫⁻ w, ENNReal.ofReal (gauss1 s (u - w)) = 1 := by
  have hi : Integrable (fun w => gauss1 s (u - w)) :=
    Integrable.of_integral_ne_zero (by rw [integral_gauss1_sub hs]; exact one_ne_zero)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => gauss1_nonneg _ _), integral_gauss1_sub hs,
    ENNReal.ofReal_one]

/-- Both image families have mass at most `1` on `(a, a+L]`. -/
lemma lintegral_imgSum_le {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (u : ℝ) :
    ∫⁻ w in Ioc a (a + L), imgSum L s (u - w) ≤ 1 ∧
      ∫⁻ w in Ioc a (a + L), imgSum L s (u + w - 2 * a) ≤ 1 := by
  have hfold := lintegral_fold (a := a) hL (fun w' => ENNReal.ofReal (gauss1 s (u - w')))
  rw [lintegral_ofReal_gauss1_sub hs] at hfold
  have hg : Continuous (gauss1 s) := continuous_gauss1 s
  have hmeas : ∀ f : ℝ → ℝ, Continuous f →
      AEMeasurable (fun w => ENNReal.ofReal (gauss1 s (f w))) (volume.restrict (Ioc a (a + L))) :=
    fun f hf => (ENNReal.measurable_ofReal.comp (hg.comp hf).measurable).aemeasurable
  constructor
  · unfold imgSum
    rw [lintegral_tsum fun (n : ℤ) => hmeas (fun w => u - w + 2 * n * L) (by fun_prop)]
    refine le_trans (le_of_eq ?_) ((le_self_add).trans hfold.le)
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ∫⁻ w in Ioc a (a + L),
      ENNReal.ofReal (gauss1 s (u - (w + 2 * n * L))))]
    congr 1; funext n; congr 1; funext w
    rw [show ((Equiv.neg ℤ) n : ℤ) = -n from rfl]; congr 2; push_cast; ring
  · unfold imgSum
    rw [lintegral_tsum fun (n : ℤ) => hmeas (fun w => u + w - 2 * a + 2 * n * L) (by fun_prop)]
    refine le_trans (le_of_eq ?_) ((le_add_self).trans hfold.le)
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ∫⁻ w in Ioc a (a + L),
      ENNReal.ofReal (gauss1 s (u - (2 * a - w + 2 * n * L))))]
    congr 1; funext n; congr 1; funext w
    rw [show ((Equiv.neg ℤ) n : ℤ) = -n from rfl]; congr 2; push_cast; ring

/-- **`L¹` bound, interval**: `∫_{(a,a+L]} |q_s(u,w)| dw ≤ 2`. -/
theorem lintegral_abs_intervalDirKernel_le {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (u : ℝ) :
    ∫⁻ w in Ioc a (a + L), ENNReal.ofReal |intervalDirKernel a L s u w| ≤ 2 := by
  have hpt : ∀ w, ENNReal.ofReal |intervalDirKernel a L s u w| ≤
      imgSum L s (u - w) + imgSum L s (u + w - 2 * a) := by
    intro w
    rw [intervalDirKernel_eq_imgSum hs hL]
    calc ENNReal.ofReal |(imgSum L s (u - w)).toReal - (imgSum L s (u + w - 2 * a)).toReal|
        ≤ ENNReal.ofReal ((imgSum L s (u - w)).toReal + (imgSum L s (u + w - 2 * a)).toReal) := by
          refine ENNReal.ofReal_le_ofReal ((abs_sub _ _).trans ?_)
          rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]
      _ = _ := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal (imgSum_ne_top hs hL _),
            ENNReal.ofReal_toReal (imgSum_ne_top hs hL _)]
  have hm : Measurable (fun w => imgSum L s (u - w)) :=
    measurable_imgSum_comp L s (by fun_prop)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left hm]
  obtain ⟨h1, h2⟩ := lintegral_imgSum_le (a := a) hs hL u
  calc _ ≤ (1 : ℝ≥0∞) + 1 := add_le_add h1 h2
    _ = 2 := one_add_one_eq_two

/-- **`L¹` bound, square**: `∫_D |p^D_s(x,y)| dy ≤ 4`. -/
theorem lintegral_abs_sqDirKernel_le {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (x : ℂ) :
    ∫⁻ y in sqOpen a L, ENNReal.ofReal |sqDirKernel a L s x y| ≤ 4 := by
  have hq : ∀ c : ℝ, Measurable (fun w => ENNReal.ofReal |intervalDirKernel a L s c w|) :=
    fun c => ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (measurable_intervalDirKernel (f := fun _ => c) (g := id) hs hL measurable_const
        measurable_id))
  have e : ∀ y : ℂ, ENNReal.ofReal |sqDirKernel a L s x y| =
      ENNReal.ofReal |intervalDirKernel a L s x.re y.re| *
        ENNReal.ofReal |intervalDirKernel a L s x.im y.im| := by
    intro y; unfold sqDirKernel; rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  simp_rw [e]
  rw [sqOpen_eq_preimage]
  have := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => ENNReal.ofReal |intervalDirKernel a L s x.re p.1| *
      ENNReal.ofReal |intervalDirKernel a L s x.im p.2|) (Ioo a (a + L) ×ˢ Ioo a (a + L))
  simp only [Complex.measurableEquivRealProd_apply] at this
  rw [this, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (hq _).aemeasurable (hq _).aemeasurable]
  have h1 : ∀ c : ℝ, ∫⁻ w in Ioo a (a + L), ENNReal.ofReal |intervalDirKernel a L s c w| ≤ 2 :=
    fun c => (lintegral_mono_set Ioo_subset_Ioc_self).trans
      (lintegral_abs_intervalDirKernel_le hs hL c)
  calc _ ≤ (2 : ℝ≥0∞) * 2 := mul_le_mul' (h1 _) (h1 _)
    _ = 4 := by norm_num

end HeatSq
end LQGMetric
