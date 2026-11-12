/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P29Third at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P29Second
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareLip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Prop 29, third term: Lipschitz bounds for the killed kernel at large times
(task P2-DDDFP29, WP-110)

DDDF (arXiv:1904.08021), `tightness.tex:1590–1596`: for `η²_t(x) = √π ∫_{1−t}^∞ ∫_D
(p_{t/2} * p^D_{s/2})(x, y) W(dy, ds)`, `E(η²_t(x) − η²_t(x'))² ≤ C|x − x'|` ("Similarly").
The input is a Lipschitz bound for `x ↦ (p_{t/2} * p^D_{s/2})(x, y)` with constant decaying in
`s`, uniformly in `t`. Here (own elementary argument, the paper gives none):

* `abs_indicator_intervalDirKernel_sub_le`: `u ↦ 1_{(a,a+L)}(u) q_r(u,v)` is Lipschitz on `ℝ`
  with constant `C e^{−π²r/(2L²)}` (`r ≥ r₀ > 0`), since `q_r(·,v)` is Lipschitz
  (`abs_intervalDirKernel_sub_sub_le`) and vanishes at `a` and `a + L`;
* `abs_sqKer_sub_le`: `y' ↦ 1_D(y') p^D_r(y', y)` is Lipschitz on `ℂ` with constant
  `2 M Λ`, `M, Λ = O(e^{−π²r/(2L²)})`;
* `abs_conv_sqKer_sub_le`: convolving with `p_t` keeps the Lipschitz constant (translation
  invariance of Lebesgue measure and `∫ p_t = 1`).
-/

noncomputable section

open MeasureTheory Real Set

namespace LQGMetric
namespace HeatSq

lemma lipConst_nonneg {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀) : 0 ≤ lipConst L s₀ := by
  unfold lipConst
  have : 0 ≤ ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2) * s₀) / 2) ^ k.natAbs :=
    tsum_nonneg fun _ => by positivity
  positivity

lemma decayConst_nonneg {L s₀ : ℝ} (hL : 0 < L) : 0 ≤ decayConst L s₀ := by
  unfold decayConst
  have : 0 ≤ ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2) * s₀)) ^ k.natAbs :=
    tsum_nonneg fun _ => by positivity
  positivity

/-- The one-dimensional killed kernel extended by `0` off `(a, a+L)`. -/
def ivKer (a L r v u : ℝ) : ℝ := (Ioo a (a + L)).indicator (fun w => intervalDirKernel a L r w v) u

lemma abs_ivKer_le {a L r r₀ : ℝ} (hL : 0 < L) (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (v u : ℝ) :
    |ivKer a L r v u| ≤ decayConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r) := by
  unfold ivKer
  by_cases hu : u ∈ Ioo a (a + L)
  · rw [indicator_of_mem hu]; exact abs_intervalDirKernel_le_exp hL hr₀ hr u v
  · rw [indicator_of_notMem hu, abs_zero]
    exact mul_nonneg (decayConst_nonneg hL) (Real.exp_pos _).le

/-- `u ↦ 1_{(a,a+L)}(u) q_r(u,v)` is Lipschitz with constant `Λ = C e^{−π²r/(2L²)}`. -/
theorem abs_ivKer_sub_le {a L r r₀ : ℝ} (hL : 0 < L) (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (v u u' : ℝ) :
    |ivKer a L r v u - ivKer a L r v u'| ≤
      lipConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r) * |u - u'| := by
  set Λ := lipConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r)
  have hΛ : 0 ≤ Λ := mul_nonneg (lipConst_nonneg hL hr₀) (Real.exp_pos _).le
  have hr0 : 0 < r := hr₀.trans_le hr
  have hq : ∀ w w', |intervalDirKernel a L r w v - intervalDirKernel a L r w' v| ≤ Λ * |w - w'| :=
    fun w w' => abs_intervalDirKernel_sub_sub_le hL hr₀ hr w w' v
  -- one point inside, one outside
  have key : ∀ w ∈ Ioo a (a + L), ∀ w' ∉ Ioo a (a + L),
      |intervalDirKernel a L r w v| ≤ Λ * |w - w'| := by
    intro w hw w' hw'
    simp only [mem_Ioo, not_and_or, not_lt] at hw'
    rcases hw' with h | h
    · have := hq w a
      rw [intervalDirKernel_left hr0 hL, sub_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hΛ)
      rw [abs_of_pos (by linarith [hw.1]), abs_of_pos (by linarith [hw.1])]; linarith
    · have := hq w (a + L)
      rw [intervalDirKernel_right hr0 hL, sub_zero] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hΛ)
      rw [abs_of_neg (by linarith [hw.2]), abs_of_neg (by linarith [hw.2])]; linarith
  unfold ivKer
  by_cases hu : u ∈ Ioo a (a + L) <;> by_cases hu' : u' ∈ Ioo a (a + L)
  · rw [indicator_of_mem hu, indicator_of_mem hu']; exact hq u u'
  · rw [indicator_of_mem hu, indicator_of_notMem hu', sub_zero]; exact key u hu u' hu'
  · rw [indicator_of_notMem hu, indicator_of_mem hu', zero_sub, abs_neg, abs_sub_comm]
    exact key u' hu' u hu
  · rw [indicator_of_notMem hu, indicator_of_notMem hu', sub_zero, abs_zero]
    exact mul_nonneg hΛ (abs_nonneg _)

/-- The square kernel extended by `0` off `D`: `1_D(y') p^D_r(y', y)`. -/
def sqKer (a L r : ℝ) (y y' : ℂ) : ℝ := ivKer a L r y.re y'.re * ivKer a L r y.im y'.im

lemma sqKer_eq_indicator (a L r : ℝ) (y y' : ℂ) :
    sqKer a L r y y' = (sqOpen a L).indicator (fun z => sqDirKernel a L r z y) y' := by
  unfold sqKer ivKer sqDirKernel
  by_cases h1 : y'.re ∈ Ioo a (a + L) <;> by_cases h2 : y'.im ∈ Ioo a (a + L)
  · rw [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem]
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  all_goals
    rw [indicator_of_notMem (show y' ∉ sqOpen a L from fun h => by
      obtain ⟨h1', h2', h3', h4'⟩ := h
      first | exact h1 ⟨h1', h2'⟩ | exact h2 ⟨h3', h4'⟩)]
    simp [indicator_of_notMem, h1, h2]

/-- **Lipschitz bound for the extended square kernel**:
`|1_D(z) p^D_r(z,y) − 1_D(z') p^D_r(z',y)| ≤ 2MΛ |z − z'|`. -/
theorem abs_sqKer_sub_le {a L r r₀ : ℝ} (hL : 0 < L) (hr₀ : 0 < r₀) (hr : r₀ ≤ r)
    (y z z' : ℂ) :
    |sqKer a L r y z - sqKer a L r y z'| ≤
      2 * (decayConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r)) *
        (lipConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r)) * ‖z - z'‖ := by
  set M := decayConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r)
  set Λ := lipConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r)
  have hΛ : 0 ≤ Λ := mul_nonneg (lipConst_nonneg hL hr₀) (Real.exp_pos _).le
  have hM : 0 ≤ M := mul_nonneg (decayConst_nonneg hL) (Real.exp_pos _).le
  have hre : |z.re - z'.re| ≤ ‖z - z'‖ := by
    have := Complex.abs_re_le_norm (z - z'); simpa using this
  have him : |z.im - z'.im| ≤ ‖z - z'‖ := by
    have := Complex.abs_im_le_norm (z - z'); simpa using this
  unfold sqKer
  rw [show ivKer a L r y.re z.re * ivKer a L r y.im z.im -
      ivKer a L r y.re z'.re * ivKer a L r y.im z'.im =
      (ivKer a L r y.re z.re - ivKer a L r y.re z'.re) * ivKer a L r y.im z.im +
        ivKer a L r y.re z'.re * (ivKer a L r y.im z.im - ivKer a L r y.im z'.im) by ring]
  have e1 : |(ivKer a L r y.re z.re - ivKer a L r y.re z'.re) * ivKer a L r y.im z.im| ≤
      (Λ * ‖z - z'‖) * M := by
    rw [abs_mul]
    exact mul_le_mul ((abs_ivKer_sub_le hL hr₀ hr _ _ _).trans
      (mul_le_mul_of_nonneg_left hre hΛ)) (abs_ivKer_le hL hr₀ hr _ _) (abs_nonneg _)
      (by positivity)
  have e2 : |ivKer a L r y.re z'.re * (ivKer a L r y.im z.im - ivKer a L r y.im z'.im)| ≤
      M * (Λ * ‖z - z'‖) := by
    rw [abs_mul]
    exact mul_le_mul (abs_ivKer_le hL hr₀ hr _ _) ((abs_ivKer_sub_le hL hr₀ hr _ _ _).trans
      (mul_le_mul_of_nonneg_left him hΛ)) (abs_nonneg _) hM
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (Λ * ‖z - z'‖) * M + M * (Λ * ‖z - z'‖) := add_le_add e1 e2
    _ = _ := by ring

/-- Convolution with the heat kernel preserves Lipschitz bounds. -/
theorem abs_integral_heatKernel_mul_sub_le {t : ℝ} (ht : 0 < t) {F : ℂ → ℝ}
    (hFm : Measurable F) {M Λ : ℝ} (hFb : ∀ z, |F z| ≤ M)
    (hFl : ∀ z z', |F z - F z'| ≤ Λ * ‖z - z'‖) (x x' : ℂ) :
    |(∫ y', heatKernel t x y' * F y') - ∫ y', heatKernel t x' y' * F y'| ≤ Λ * ‖x - x'‖ := by
  have hp : Integrable (heatKernel t 0) := integrable_heatKernel t ht 0
  have hpc : Continuous (heatKernel t 0) := by unfold heatKernel; fun_prop
  have htr : ∀ z : ℂ, ∫ y', heatKernel t z y' * F y' = ∫ w, heatKernel t 0 w * F (z + w) := by
    intro z
    rw [← integral_add_left_eq_self (fun y' => heatKernel t z y' * F y') z]
    simp only [heatKernel_eq_zero_center]
  have hint : ∀ z : ℂ, Integrable (fun w => heatKernel t 0 w * F (z + w)) := fun z =>
    Integrable.mono' (hp.mul_const M) ((hpc.measurable.mul
      (hFm.comp (measurable_const.add measurable_id))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg t ht.le 0 w)]
        exact mul_le_mul_of_nonneg_left (hFb _) (heatKernel_nonneg t ht.le 0 w))
  rw [htr, htr, ← integral_sub (hint x) (hint x')]
  have hb := norm_integral_le_of_norm_le (hp.mul_const (Λ * ‖x - x'‖))
    (f := fun w => heatKernel t 0 w * F (x + w) - heatKernel t 0 w * F (x' + w))
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (heatKernel_nonneg t ht.le 0 w)]
      refine mul_le_mul_of_nonneg_left ((hFl _ _).trans_eq ?_) (heatKernel_nonneg t ht.le 0 w)
      congr 2; ring)
  rw [Real.norm_eq_abs, integral_mul_const, integral_heatKernel t ht, one_mul] at hb
  exact hb

lemma measurable_sqKer {a L r : ℝ} (hr : 0 < r) (hL : 0 < L) (y : ℂ) :
    Measurable (sqKer a L r y) := by
  have : sqKer a L r y = (sqOpen a L).indicator (fun z => sqDirKernel a L r z y) := by
    funext y'; exact sqKer_eq_indicator a L r y y'
  rw [this]
  exact (measurable_sqDirKernel_left hr hL y).indicator (measurableSet_sqOpen a L)

/-- **Third-term kernel, Lipschitz in `x`** (DDDF `tightness.tex:1593`): for `r ≥ r₀ > 0` and
every `t > 0`, `x ↦ ∫_D p_t(x,y') p^D_r(y',y) dy'` is Lipschitz with constant `2MΛ`,
`M, Λ = O(e^{−π²r/(2L²)})`, uniformly in `t` and `y`. -/
theorem abs_conv_sqKer_sub_le {a L t r r₀ : ℝ} (hL : 0 < L) (ht : 0 < t) (hr₀ : 0 < r₀)
    (hr : r₀ ≤ r) (y x x' : ℂ) :
    |(∫ y' in sqOpen a L, heatKernel t x y' * sqDirKernel a L r y' y) -
        ∫ y' in sqOpen a L, heatKernel t x' y' * sqDirKernel a L r y' y| ≤
      2 * (decayConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r)) *
        (lipConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r)) * ‖x - x'‖ := by
  have hr0 : 0 < r := hr₀.trans_le hr
  have e : ∀ z : ℂ, ∫ y' in sqOpen a L, heatKernel t z y' * sqDirKernel a L r y' y =
      ∫ y', heatKernel t z y' * sqKer a L r y y' := by
    intro z
    rw [← integral_indicator (measurableSet_sqOpen a L)]
    congr 1; funext y'
    rw [sqKer_eq_indicator]
    by_cases h : y' ∈ sqOpen a L
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  rw [e, e]
  refine abs_integral_heatKernel_mul_sub_le ht (measurable_sqKer hr0 hL y)
    (M := (decayConst L r₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * r)) ^ 2) (fun z => ?_)
    (fun z z' => abs_sqKer_sub_le hL hr₀ hr y z z') x x'
  unfold sqKer
  rw [abs_mul, sq]
  exact mul_le_mul (abs_ivKer_le hL hr₀ hr _ _) (abs_ivKer_le hL hr₀ hr _ _) (abs_nonneg _)
    (mul_nonneg (decayConst_nonneg hL) (Real.exp_pos _).le)

lemma volume_sqOpen (a L : ℝ) (hL : 0 ≤ L) : volume (sqOpen a L) = ENNReal.ofReal (L ^ 2) := by
  rw [sqOpen_eq_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, ← ENNReal.ofReal_mul (by linarith)]
  congr 1; ring

/-- DDDF's third-term kernel `(p_{t/2} * p^D_{s/2})(z, y) = ∫_D p_{t/2}(z,y') p^D_{s/2}(y',y) dy'`. -/
def thirdKer (a L t s : ℝ) (z y : ℂ) : ℝ :=
  ∫ y' in sqOpen a L, heatKernel (t / 2) z y' * sqDirKernel a L (s / 2) y' y

/-- The constant of the third-term bound. -/
def thirdConst (L s₁ : ℝ) : ℝ :=
  (2 * decayConst L (s₁ / 2) * lipConst L (s₁ / 2)) ^ 2 * L ^ 2 *
    (Real.exp (-(2 * (π ^ 2 / (2 * L ^ 2))) * s₁) / (2 * (π ^ 2 / (2 * L ^ 2))))

/-- **Third term, increments** (DDDF `tightness.tex:1590–1596`): for `t > 0`, `s₁ > 0`,
`∫_{s₁}^∞ ∫_D ((p_{t/2} * p^D_{s/2})(x,y) − (p_{t/2} * p^D_{s/2})(x',y))² dy ds ≤ C |x − x'|²`
with `C = thirdConst L s₁` independent of `t` (DDDF: `s₁ = 1 − t ≥ 1/2`). -/
theorem lintegral_thirdTerm_incr_le {a L t s₁ : ℝ} (hL : 0 < L) (ht : 0 < t) (hs₁ : 0 < s₁)
    (x x' : ℂ) :
    ∫⁻ s in Ioi s₁, ∫⁻ y in sqOpen a L,
        ENNReal.ofReal ((thirdKer a L t s x y - thirdKer a L t s x' y) ^ 2) ≤
      ENNReal.ofReal (thirdConst L s₁ * ‖x - x'‖ ^ 2) := by
  set l := π ^ 2 / (2 * L ^ 2) with hl
  have hl0 : 0 < l := by positivity
  set c := 2 * decayConst L (s₁ / 2) * lipConst L (s₁ / 2)
  have hc : 0 ≤ c := by
    have := decayConst_nonneg (s₀ := s₁ / 2) hL
    have := lipConst_nonneg hL (by positivity : 0 < s₁ / 2)
    positivity
  have hpt : ∀ s ∈ Ioi s₁, ∫⁻ y in sqOpen a L,
      ENNReal.ofReal ((thirdKer a L t s x y - thirdKer a L t s x' y) ^ 2) ≤
        ENNReal.ofReal (c ^ 2 * ‖x - x'‖ ^ 2 * L ^ 2 * Real.exp (-(2 * l) * s)) := by
    intro s hs
    have hb : ∀ y, (thirdKer a L t s x y - thirdKer a L t s x' y) ^ 2 ≤
        c ^ 2 * ‖x - x'‖ ^ 2 * Real.exp (-(2 * l) * s) := by
      intro y
      have h := abs_conv_sqKer_sub_le (a := a) hL (half_pos ht) (half_pos hs₁)
        (by linarith [mem_Ioi.mp hs] : s₁ / 2 ≤ s / 2) y x x'
      have he : Real.exp (-l * (s / 2)) * Real.exp (-l * (s / 2)) = Real.exp (-l * s) := by
        rw [← Real.exp_add]; ring_nf
      have h' : |thirdKer a L t s x y - thirdKer a L t s x' y| ≤
          c * Real.exp (-l * s) * ‖x - x'‖ := by
        refine h.trans_eq ?_
        rw [← he]; ring
      have he2 : Real.exp (-l * s) ^ 2 = Real.exp (-(2 * l) * s) := by
        rw [← Real.exp_nat_mul]; ring_nf
      calc (thirdKer a L t s x y - thirdKer a L t s x' y) ^ 2
          = |thirdKer a L t s x y - thirdKer a L t s x' y| ^ 2 := (sq_abs _).symm
        _ ≤ (c * Real.exp (-l * s) * ‖x - x'‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h' 2
        _ = _ := by rw [mul_pow, mul_pow, he2]; ring
    refine (setLIntegral_mono' (measurableSet_sqOpen a L)
      (fun y _ => ENNReal.ofReal_le_ofReal (hb y))).trans_eq ?_
    rw [setLIntegral_const, volume_sqOpen a L hL.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  refine (setLIntegral_mono' measurableSet_Ioi hpt).trans ?_
  have hneg : -(2 * l) < 0 := by linarith
  have hint : IntegrableOn (fun s => c ^ 2 * ‖x - x'‖ ^ 2 * L ^ 2 * Real.exp (-(2 * l) * s))
      (Ioi s₁) := (integrableOn_exp_mul_Ioi hneg s₁).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun s => by
    positivity), integral_const_mul, integral_exp_mul_Ioi hneg]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold thirdConst
  simp only [c, hl]
  field_simp

lemma abs_integral_heatKernel_mul_le {t : ℝ} (ht : 0 < t) {F : ℂ → ℝ} {B : ℝ}
    (hFb : ∀ z, |F z| ≤ B) (x : ℂ) : |∫ y', heatKernel t x y' * F y'| ≤ B := by
  have hb := norm_integral_le_of_norm_le ((integrable_heatKernel t ht x).mul_const B)
    (f := fun y' => heatKernel t x y' * F y') (Filter.Eventually.of_forall fun y' => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg t ht.le x y')]
      exact mul_le_mul_of_nonneg_left (hFb y') (heatKernel_nonneg t ht.le x y'))
  rwa [Real.norm_eq_abs, integral_mul_const, integral_heatKernel t ht, one_mul] at hb

/-- The constant of the third-term variance bound. -/
def thirdVarConst (L s₁ : ℝ) : ℝ :=
  decayConst L (s₁ / 2) ^ 4 * L ^ 2 *
    (Real.exp (-(2 * (π ^ 2 / (2 * L ^ 2))) * s₁) / (2 * (π ^ 2 / (2 * L ^ 2))))

/-- **Third term, variance** (DDDF `tightness.tex:1596`, "the pointwise variance is uniformly
bounded"): `∫_{s₁}^∞ ∫_D (p_{t/2} * p^D_{s/2})(x,y)² dy ds ≤ C`, uniformly in `t > 0` and `x`. -/
theorem lintegral_thirdTerm_var_le {a L t s₁ : ℝ} (hL : 0 < L) (ht : 0 < t) (hs₁ : 0 < s₁)
    (x : ℂ) :
    ∫⁻ s in Ioi s₁, ∫⁻ y in sqOpen a L, ENNReal.ofReal (thirdKer a L t s x y ^ 2) ≤
      ENNReal.ofReal (thirdVarConst L s₁) := by
  set l := π ^ 2 / (2 * L ^ 2) with hl
  have hl0 : 0 < l := by positivity
  set m := decayConst L (s₁ / 2)
  have hm : 0 ≤ m := decayConst_nonneg hL
  have hpt : ∀ s ∈ Ioi s₁, ∫⁻ y in sqOpen a L, ENNReal.ofReal (thirdKer a L t s x y ^ 2) ≤
      ENNReal.ofReal (m ^ 4 * L ^ 2 * Real.exp (-(2 * l) * s)) := by
    intro s hs
    have hss : s₁ / 2 ≤ s / 2 := by linarith [mem_Ioi.mp hs]
    have hs0 : 0 < s / 2 := by linarith [mem_Ioi.mp hs]
    have hb : ∀ y, thirdKer a L t s x y ^ 2 ≤ m ^ 4 * Real.exp (-(2 * l) * s) := by
      intro y
      have hK : |thirdKer a L t s x y| ≤ (m * Real.exp (-l * (s / 2))) ^ 2 := by
        unfold thirdKer
        rw [← integral_indicator (measurableSet_sqOpen a L)]
        have e : (sqOpen a L).indicator (fun y' => heatKernel (t / 2) x y' *
            sqDirKernel a L (s / 2) y' y) = fun y' => heatKernel (t / 2) x y' *
            sqKer a L (s / 2) y y' := by
          funext y'; rw [sqKer_eq_indicator]
          by_cases h : y' ∈ sqOpen a L
          · simp [indicator_of_mem h]
          · simp [indicator_of_notMem h]
        rw [e]
        refine abs_integral_heatKernel_mul_le (half_pos ht) (fun z => ?_) x
        unfold sqKer
        rw [abs_mul, sq]
        exact mul_le_mul (abs_ivKer_le hL (half_pos hs₁) hss _ _)
          (abs_ivKer_le hL (half_pos hs₁) hss _ _) (abs_nonneg _)
          (mul_nonneg hm (Real.exp_pos _).le)
      have he : (Real.exp (-l * (s / 2))) ^ 4 = Real.exp (-(2 * l) * s) := by
        rw [← Real.exp_nat_mul]; ring_nf
      calc thirdKer a L t s x y ^ 2 = |thirdKer a L t s x y| ^ 2 := (sq_abs _).symm
        _ ≤ ((m * Real.exp (-l * (s / 2))) ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hK 2
        _ = _ := by rw [← he]; ring
    refine (setLIntegral_mono' (measurableSet_sqOpen a L)
      (fun y _ => ENNReal.ofReal_le_ofReal (hb y))).trans_eq ?_
    rw [setLIntegral_const, volume_sqOpen a L hL.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  refine (setLIntegral_mono' measurableSet_Ioi hpt).trans ?_
  have hneg : -(2 * l) < 0 := by linarith
  have hint : IntegrableOn (fun s => m ^ 4 * L ^ 2 * Real.exp (-(2 * l) * s)) (Ioi s₁) :=
    (integrableOn_exp_mul_Ioi hneg s₁).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun s => by
    positivity), integral_const_mul, integral_exp_mul_Ioi hneg]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold thirdVarConst
  simp only [m, hl]
  field_simp

end HeatSq
end LQGMetric
