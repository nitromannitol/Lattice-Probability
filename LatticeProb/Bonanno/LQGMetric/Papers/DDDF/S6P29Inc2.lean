/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P29Inc2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29Inc
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29First

/-!
# DDDF Prop 29, first-term increments: the `L¹` bound in `y` (task P2-DDDFP29c)

DDDF arXiv:1904.08021, `tightness.tex` DD:1571–1576 (first term of (6.97)). Own route
(DEVIATIONS: replaces the paper's sketch, which uses (6.96) also near `∂D`):

1. `Ek r z y = p^D_r(clamp z, y) − p_r(z, y)` (`clamp z` the nearest point of `D̄`, so
   `p^D_r(clamp z, y) = 1_D(z) p^D_r(z,y)` by the Dirichlet boundary values, `sqDirKernel_clampSq`).
2. Chapman–Kolmogorov and translation: `p_τ * p^D_r(x,y) − p_{τ+r}(x,y) = ∫ p_τ(0,w) Ek r (x−w) y dw`
   (`conv_sub_heat_eq`).
3. `∫_D |Ek r z y − Ek r z' y| dy ≤ 6 c₀ |z − z'| / √r` for all `z, z'` (`lintegral_abs_Ek_sub_le`;
   product structure and the one-dimensional bounds of `S6P29Inc`).
4. Hence `∫_D |firstKer t s x y − firstKer t s x' y| dy ≤ 6 c₀ √2 |x − x'| / √s`
   (`lintegral_abs_firstKer_sub_le`), uniformly in `t > 0` and for all `x, x'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace P29WN

open HeatSq

/-- The nearest point of the closed square `[a, a+L]²`. -/
def clampSq (a L : ℝ) (z : ℂ) : ℂ := ⟨clampI a L z.re, clampI a L z.im⟩

lemma sqDirKernel_clampSq {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (z y : ℂ) :
    sqDirKernel a L r (clampSq a L z) y =
      (sqOpen a L).indicator (fun z => sqDirKernel a L r z y) z := by
  by_cases hz : z ∈ sqOpen a L
  · rw [indicator_of_mem hz]
    have h1 : clampI a L z.re = z.re := clampI_of_mem ⟨hz.1, hz.2.1⟩
    have h2 : clampI a L z.im = z.im := clampI_of_mem ⟨hz.2.2.1, hz.2.2.2⟩
    unfold sqDirKernel clampSq
    dsimp only
    rw [h1, h2]
  · rw [indicator_of_notMem hz]
    unfold sqDirKernel clampSq
    dsimp only
    by_cases hre : z.re ∈ Ioo a (a + L)
    · have him : z.im ∉ Ioo a (a + L) := fun him => hz ⟨hre.1, hre.2, him.1, him.2⟩
      rw [intervalDirKernel_clampI_of_not_mem hr hL him, mul_zero]
    · rw [intervalDirKernel_clampI_of_not_mem hr hL hre, zero_mul]

lemma continuous_clampI (a L : ℝ) : Continuous (clampI a L) := by
  unfold clampI; fun_prop

/-- `∫_D F(y.re) G(y.im) dy = (∫_I F)(∫_I G)`. -/
lemma lintegral_sqOpen_mul (a L : ℝ) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ y in sqOpen a L, F y.re * G y.im =
      (∫⁻ u in Ioo a (a + L), F u) * ∫⁻ v in Ioo a (a + L), G v := by
  rw [sqOpen_eq_preimage]
  have := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => F p.1 * G p.2) (Ioo a (a + L) ×ˢ Ioo a (a + L))
  simp only [Complex.measurableEquivRealProd_apply] at this
  rw [this, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul hF.aemeasurable hG.aemeasurable]

/-- The comparison kernel `p^D_r(clamp z, y) − p_r(z, y)`. -/
def Ek (a L r : ℝ) (z y : ℂ) : ℝ := sqDirKernel a L r (clampSq a L z) y - heatKernel r z y

lemma measurable_Ek {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) :
    Measurable (fun p : ℂ × ℂ => Ek a L r p.1 p.2) := by
  have hc := (continuous_clampI a L).measurable
  unfold Ek sqDirKernel clampSq
  dsimp only
  refine ((measurable_intervalDirKernel hr hL (hc.comp (Complex.measurable_re.comp measurable_fst))
    (Complex.measurable_re.comp measurable_snd)).mul
    (measurable_intervalDirKernel hr hL (hc.comp (Complex.measurable_im.comp measurable_fst))
      (Complex.measurable_im.comp measurable_snd))).sub ?_
  exact (show Continuous (fun p : ℂ × ℂ => heatKernel r p.1 p.2) by
    unfold heatKernel; fun_prop).measurable

lemma measurable_Ek_shift {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (x : ℂ) :
    Measurable (fun p : ℂ × ℂ => Ek a L r (x - p.2) p.1) := by
  have hc : Measurable (fun p : ℂ × ℂ => (x - p.2, p.1)) :=
    (measurable_const.sub measurable_snd).prodMk measurable_fst
  have := (measurable_Ek (a := a) (L := L) hr hL).comp hc
  simpa only [Function.comp_def] using this

lemma meas_ofReal_abs_q {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (c c' : ℝ) :
    Measurable (fun v => ENNReal.ofReal |intervalDirKernel a L r c v -
      intervalDirKernel a L r c' v|) :=
  ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    ((measurable_intervalDirKernel (f := fun _ => c) (g := id) hr hL measurable_const
      measurable_id).sub (measurable_intervalDirKernel (f := fun _ => c') (g := id) hr hL
      measurable_const measurable_id)))

lemma meas_ofReal_abs_q1 {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (c : ℝ) :
    Measurable (fun v => ENNReal.ofReal |intervalDirKernel a L r c v|) :=
  ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    (measurable_intervalDirKernel (f := fun _ => c) (g := id) hr hL measurable_const
      measurable_id))

lemma meas_ofReal_abs_g (r c c' : ℝ) :
    Measurable (fun v => ENNReal.ofReal |gauss1 r (c - v) - gauss1 r (c' - v)|) :=
  ENNReal.measurable_ofReal.comp (continuous_abs.comp
    (((continuous_gauss1 r).comp (continuous_sub_left c)).sub
      ((continuous_gauss1 r).comp (continuous_sub_left c')))).measurable

lemma meas_ofReal_g (r c : ℝ) : Measurable (fun v => ENNReal.ofReal (gauss1 r (c - v))) :=
  ENNReal.measurable_ofReal.comp ((continuous_gauss1 r).comp (continuous_sub_left c)).measurable

lemma meas_prod {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun y : ℂ => F y.re * G y.im) :=
  (hF.comp Complex.measurable_re).mul (hG.comp Complex.measurable_im)

lemma lintegral_add4 {μ : Measure ℂ} {f1 f2 f3 f4 : ℂ → ℝ≥0∞} (h1 : Measurable f1)
    (h2 : Measurable f2) (h3 : Measurable f3) :
    ∫⁻ y, f1 y + f2 y + f3 y + f4 y ∂μ =
      (∫⁻ y, f1 y ∂μ) + (∫⁻ y, f2 y ∂μ) + (∫⁻ y, f3 y ∂μ) + ∫⁻ y, f4 y ∂μ := by
  rw [lintegral_add_left (f := fun y => f1 y + f2 y + f3 y) ((h1.add h2).add h3),
    lintegral_add_left (f := fun y => f1 y + f2 y) (h1.add h2), lintegral_add_left h1]

lemma ofReal_add4_le (a b c d : ℝ) : ENNReal.ofReal (a + b + c + d) ≤
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d :=
  calc ENNReal.ofReal (a + b + c + d) ≤ ENNReal.ofReal (a + b + c) + ENNReal.ofReal d :=
        ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (a + b) + ENNReal.ofReal c + ENNReal.ofReal d := by
        gcongr; exact ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr; exact ENNReal.ofReal_add_le

/-- Real inequality behind the product rule. -/
lemma abs_prod_sub_le (A1 A2 A1' A2' G1 G2 G1' G2' : ℝ) (hG2 : 0 ≤ G2) (hG1' : 0 ≤ G1') :
    |A1 * A2 - G1 * G2 - (A1' * A2' - G1' * G2')| ≤
      |A1 - A1'| * |A2| + |A1'| * |A2 - A2'| + |G1 - G1'| * G2 + G1' * |G2 - G2'| := by
  have e : A1 * A2 - G1 * G2 - (A1' * A2' - G1' * G2') =
      (A1 - A1') * A2 + A1' * (A2 - A2') - ((G1 - G1') * G2 + G1' * (G2 - G2')) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) (abs_add_le _ _)).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hG2, abs_of_nonneg hG1']
  ring

/-- **Step 3**: `∫_D |Ek r z y − Ek r z' y| dy ≤ 6 c₀ |z − z'| / √r`. -/
theorem lintegral_abs_Ek_sub_le {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (z z' : ℂ) :
    ∫⁻ y in sqOpen a L, ENNReal.ofReal |Ek a L r z y - Ek a L r z' y| ≤
      ENNReal.ofReal (6 * (incConst / Real.sqrt r * ‖z - z'‖)) := by
  set B := incConst / Real.sqrt r * ‖z - z'‖ with hB
  have hB0 : 0 ≤ B := by
    have := two_le_incConst; positivity
  set q := intervalDirKernel a L r with hq
  set u1 := clampI a L z.re
  set u1' := clampI a L z'.re
  set u2 := clampI a L z.im
  set u2' := clampI a L z'.im
  have hEk : ∀ w y : ℂ, Ek a L r w y = q (clampI a L w.re) y.re * q (clampI a L w.im) y.im -
      gauss1 r (w.re - y.re) * gauss1 r (w.im - y.im) := by
    intro w y; unfold Ek sqDirKernel clampSq; rw [gauss1_mul_gauss1 r hr]
  have hpt : ∀ y : ℂ, ENNReal.ofReal |Ek a L r z y - Ek a L r z' y| ≤
      ENNReal.ofReal |q u1 y.re - q u1' y.re| * ENNReal.ofReal |q u2 y.im| +
      ENNReal.ofReal |q u1' y.re| * ENNReal.ofReal |q u2 y.im - q u2' y.im| +
      ENNReal.ofReal |gauss1 r (z.re - y.re) - gauss1 r (z'.re - y.re)| *
        ENNReal.ofReal (gauss1 r (z.im - y.im)) +
      ENNReal.ofReal (gauss1 r (z'.re - y.re)) *
        ENNReal.ofReal |gauss1 r (z.im - y.im) - gauss1 r (z'.im - y.im)| := by
    intro y
    rw [hEk, hEk]
    refine (ENNReal.ofReal_le_ofReal (abs_prod_sub_le _ _ _ _ _ _ _ _ (gauss1_nonneg _ _)
      (gauss1_nonneg _ _))).trans ?_
    refine (ofReal_add4_le _ _ _ _).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (abs_nonneg _),
      ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (gauss1_nonneg _ _)]
  have hm1 := meas_ofReal_abs_q (a := a) hr hL u1 u1'
  have hm2 := meas_ofReal_abs_q1 (a := a) hr hL u2
  have hm3 := meas_ofReal_abs_q1 (a := a) hr hL u1'
  have hm4 := meas_ofReal_abs_q (a := a) hr hL u2 u2'
  have hg1 := meas_ofReal_abs_g r z.re z'.re
  have hg2 := meas_ofReal_g r z.im
  have hg3 := meas_ofReal_g r z'.re
  have hg4 := meas_ofReal_abs_g r z.im z'.im
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add4 (meas_prod hm1 hm2) (meas_prod hm3 hm4) (meas_prod hg1 hg2),
    lintegral_sqOpen_mul a L hm1 hm2, lintegral_sqOpen_mul a L hm3 hm4,
    lintegral_sqOpen_mul a L hg1 hg2, lintegral_sqOpen_mul a L hg3 hg4]
  -- one-dimensional bounds
  have hre : |z.re - z'.re| ≤ ‖z - z'‖ := by
    have := Complex.abs_re_le_norm (z - z'); simpa using this
  have him : |z.im - z'.im| ≤ ‖z - z'‖ := by
    have := Complex.abs_im_le_norm (z - z'); simpa using this
  have hc0 : 0 ≤ incConst / Real.sqrt r := by have := two_le_incConst; positivity
  have hQ : ∀ c c', |c - c'| ≤ ‖z - z'‖ →
      ∫⁻ v in Ioo a (a + L), ENNReal.ofReal |q (clampI a L c) v - q (clampI a L c') v| ≤
        ENNReal.ofReal B := fun c c' hcc =>
    (lintegral_mono_set Ioo_subset_Ioc_self).trans ((intervalShift_lintegral_le hr hL _ _).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        ((abs_clampI_sub_le a L c c').trans hcc) hc0)))
  have hQ1 : ∀ c, ∫⁻ v in Ioo a (a + L), ENNReal.ofReal |q c v| ≤ 2 := fun c =>
    (lintegral_mono_set Ioo_subset_Ioc_self).trans (lintegral_abs_intervalDirKernel_le hr hL c)
  have hG : ∀ c c', |c - c'| ≤ ‖z - z'‖ →
      ∫⁻ v in Ioo a (a + L), ENNReal.ofReal |gauss1 r (c - v) - gauss1 r (c' - v)| ≤
        ENNReal.ofReal B := fun c c' hcc =>
    setLIntegral_le_lintegral _ _ |>.trans ((gaussShift_lintegral_le hr c c').trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcc hc0)))
  have hG1 : ∀ c, ∫⁻ v in Ioo a (a + L), ENNReal.ofReal (gauss1 r (c - v)) ≤ 1 := fun c =>
    (setLIntegral_le_lintegral _ _).trans (lintegral_ofReal_gauss1_sub hr c).le
  calc _ ≤ ENNReal.ofReal B * 2 + 2 * ENNReal.ofReal B + ENNReal.ofReal B * 1 +
        1 * ENNReal.ofReal B := by
        gcongr
        · exact hQ _ _ hre
        · exact hQ1 _
        · exact hQ1 _
        · exact hQ _ _ him
        · exact hG _ _ hre
        · exact hG1 _
        · exact hG1 _
        · exact hG _ _ him
    _ = ENNReal.ofReal (6 * B) := by
        rw [hB, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_mul hc0,
          ENNReal.ofReal_ofNat]; ring

lemma heatKernel_le_inv {τ : ℝ} (hτ : 0 < τ) (x y : ℂ) : heatKernel τ x y ≤ (2 * π * τ)⁻¹ := by
  unfold heatKernel
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
  rw [neg_div]; exact neg_nonpos.mpr (by positivity)

lemma integrable_heat_mul_sqDir {a L τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hL : 0 < L) (x y : ℂ) :
    Integrable (fun y' => heatKernel τ x y' * sqDirKernel a L r (clampSq a L y') y) := by
  have e : (fun y' => heatKernel τ x y' * sqDirKernel a L r (clampSq a L y') y) =
      (sqOpen a L).indicator (fun y' => heatKernel τ x y' * sqDirKernel a L r y' y) := by
    funext y'
    rw [sqDirKernel_clampSq hr hL]
    by_cases h : y' ∈ sqOpen a L
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [e, integrable_indicator_iff (measurableSet_sqOpen a L)]
  refine Integrable.bdd_mul (c := (2 * π * τ)⁻¹) (integral_abs_sqDirKernel_le hr hL y).1 ?_ ?_
  · exact (show Continuous (heatKernel τ x) by unfold heatKernel; fun_prop).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y' => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg τ hτ.le x y')]
    exact heatKernel_le_inv hτ x y'

lemma heatKernel_sub_center (τ : ℝ) (x w : ℂ) : heatKernel τ x (x - w) = heatKernel τ 0 w := by
  simp [heatKernel]

lemma integrable_heat_mul_Ek {a L τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hL : 0 < L) (x y : ℂ) :
    Integrable (fun w => heatKernel τ 0 w * Ek a L r (x - w) y) := by
  have h := ((integrable_heat_mul_sqDir (a := a) (L := L) hτ hr hL x y).sub
    (integrable_heatKernel_mul_heatKernel_ck τ r hτ hr x y)).comp_sub_left x
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Pi.sub_apply]
  rw [heatKernel_sub_center]; unfold Ek; ring

/-- **Step 2** (Chapman–Kolmogorov and translation). -/
theorem conv_sub_heat_eq {a L τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hL : 0 < L) (x y : ℂ) :
    (∫ y' in sqOpen a L, heatKernel τ x y' * sqDirKernel a L r y' y) - heatKernel (τ + r) x y =
      ∫ w, heatKernel τ 0 w * Ek a L r (x - w) y := by
  have h1 := integrable_heat_mul_sqDir (a := a) (L := L) hτ hr hL x y
  have h2 := integrable_heatKernel_mul_heatKernel_ck τ r hτ hr x y
  have e1 : ∫ y' in sqOpen a L, heatKernel τ x y' * sqDirKernel a L r y' y =
      ∫ y', heatKernel τ x y' * sqDirKernel a L r (clampSq a L y') y := by
    rw [← integral_indicator (measurableSet_sqOpen a L)]
    congr 1; funext y'
    rw [sqDirKernel_clampSq hr hL]
    by_cases h : y' ∈ sqOpen a L
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [e1, ← integral_heatKernel_mul_heatKernel_ck τ r hτ hr x y, ← integral_sub h1 h2]
  have e2 := integral_sub_left_eq_self (fun y' => heatKernel τ x y' *
    sqDirKernel a L r (clampSq a L y') y - heatKernel τ x y' * heatKernel r y' y) volume x
  rw [← e2]
  congr 1; funext w
  rw [heatKernel_sub_center]; unfold Ek; ring

lemma lintegral_ofReal_heatKernel {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ w, ENNReal.ofReal (heatKernel τ 0 w) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel τ hτ 0)
    (Filter.Eventually.of_forall fun w => heatKernel_nonneg τ hτ.le 0 w),
    integral_heatKernel τ hτ 0, ENNReal.ofReal_one]

/-- **Step 4**, convolution form. -/
theorem lintegral_abs_conv_sub_le {a L τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hL : 0 < L)
    (x x' : ℂ) :
    ∫⁻ y in sqOpen a L, ENNReal.ofReal
      |((∫ y' in sqOpen a L, heatKernel τ x y' * sqDirKernel a L r y' y) - heatKernel (τ + r) x y) -
        ((∫ y' in sqOpen a L, heatKernel τ x' y' * sqDirKernel a L r y' y) -
          heatKernel (τ + r) x' y)| ≤
      ENNReal.ofReal (6 * (incConst / Real.sqrt r * ‖x - x'‖)) := by
  set B := ENNReal.ofReal (6 * (incConst / Real.sqrt r * ‖x - x'‖))
  have hpt : ∀ y, ENNReal.ofReal
      |((∫ y' in sqOpen a L, heatKernel τ x y' * sqDirKernel a L r y' y) - heatKernel (τ + r) x y) -
        ((∫ y' in sqOpen a L, heatKernel τ x' y' * sqDirKernel a L r y' y) -
          heatKernel (τ + r) x' y)| ≤
      ∫⁻ w, ENNReal.ofReal (heatKernel τ 0 w) *
        ENNReal.ofReal |Ek a L r (x - w) y - Ek a L r (x' - w) y| := by
    intro y
    rw [conv_sub_heat_eq hτ hr hL x y, conv_sub_heat_eq hτ hr hL x' y,
      ← integral_sub (integrable_heat_mul_Ek hτ hr hL x y) (integrable_heat_mul_Ek hτ hr hL x' y),
      ← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1; funext w
    rw [← mul_sub, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg τ hτ.le 0 w),
      ENNReal.ofReal_mul (heatKernel_nonneg τ hτ.le 0 w)]
  refine (lintegral_mono hpt).trans ?_
  have hmeas : Measurable (Function.uncurry fun (y w : ℂ) => ENNReal.ofReal (heatKernel τ 0 w) *
      ENNReal.ofReal |Ek a L r (x - w) y - Ek a L r (x' - w) y|) := by
    have hG : Continuous (fun w : ℂ => heatKernel τ 0 w) := by unfold heatKernel; fun_prop
    have hE1 : Measurable (fun p : ℂ × ℂ => Ek a L r (x - p.2) p.1) :=
      measurable_Ek_shift hr hL x
    have hE2 : Measurable (fun p : ℂ × ℂ => Ek a L r (x' - p.2) p.1) :=
      measurable_Ek_shift hr hL x'
    have hG1 : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (heatKernel τ 0 p.2)) :=
      ENNReal.measurable_ofReal.comp (hG.measurable.comp measurable_snd)
    have hA : Measurable (fun p : ℂ × ℂ =>
        ENNReal.ofReal |Ek a L r (x - p.2) p.1 - Ek a L r (x' - p.2) p.1|) :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hE1.sub hE2))
    exact hG1.mul hA
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ w, ∫⁻ y in sqOpen a L, ENNReal.ofReal (heatKernel τ 0 w) *
        ENNReal.ofReal |Ek a L r (x - w) y - Ek a L r (x' - w) y|
      = ∫⁻ w, ENNReal.ofReal (heatKernel τ 0 w) * ∫⁻ y in sqOpen a L,
          ENNReal.ofReal |Ek a L r (x - w) y - Ek a L r (x' - w) y| := by
        congr 1; funext w; rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ w, ENNReal.ofReal (heatKernel τ 0 w) * B := by
        refine lintegral_mono fun w => mul_le_mul_of_nonneg_left ?_ (zero_le)
        have := lintegral_abs_Ek_sub_le (a := a) (L := L) hr hL (x - w) (x' - w)
        rwa [show x - w - (x' - w) = x - x' by ring] at this
    _ = B := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_heatKernel hτ, one_mul]

/-- **Step 4**: the `L¹(D)` increment bound for `firstKer`, uniform in `t > 0`. -/
theorem lintegral_abs_firstKer_sub_le {a L t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hL : 0 < L)
    (x x' : ℂ) :
    ∫⁻ y in sqOpen a L, ENNReal.ofReal |firstKer a L t s x y - firstKer a L t s x' y| ≤
      ENNReal.ofReal (6 * (incConst / Real.sqrt (s / 2) * ‖x - x'‖)) := by
  have := lintegral_abs_conv_sub_le (a := a) (L := L) (half_pos ht) (half_pos hs) hL x x'
  unfold firstKer thirdKer
  rwa [show (t + s) / 2 = t / 2 + s / 2 by ring]

end P29WN
end DDDF
end LQGMetric
