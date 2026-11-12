/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareGreen2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareL1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
With the product modes `φ_{jk}(z) = sin(πj(x−a)/L) sin(πk(y−a)/L)` (`HeatSq.sqMode`) and the
coefficients `ρ̂_{jk} = ∫ ρ φ_{jk}` (`HeatSq.sqCoef`):

* `HeatSq.hasSum_sqDirKernel_sine` : `p^D_s(x,y) = (4/L²) ∑ e^{−π²(j²+k²)s/(2L²)} φ_{jk}(x) φ_{jk}(y)`
  (product of the two interval series);
* `HeatSq.hasSum_integral_sqDirKernel` : `∫∫ ρ(x) p^D_s(x,y) σ(y) = (4/L²) ∑ e^{…} ρ̂_{jk} σ̂_{jk}`
  for integrable `ρ, σ` (dominated convergence, mathlib `hasSum_integral_of_dominated_convergence`);
* `HeatSq.summable_sqCoef_sq` : `∑ ρ̂_{jk}² < ∞` for bounded measurable `ρ` vanishing off the
  square (from the uniform bound `∫_D |p^D_s(x,·)| ≤ 4` and `s → 0`; this replaces Bessel's
  inequality, own elementary argument).
-/

noncomputable section

open Real MeasureTheory Set Filter Topology

namespace LQGMetric
namespace HeatSq

/-- the product Dirichlet mode `φ_{jk}` of the square `(a,a+L)²` -/
def sqMode (a L : ℝ) (p : ℕ × ℕ) (z : ℂ) : ℝ := sinMode a L p.1 z.re * sinMode a L p.2 z.im

/-- `e^{−π²(j²+k²)s/(2L²)}` -/
def sqDecay (L s : ℝ) (p : ℕ × ℕ) : ℝ := modeDecay L s p.1 * modeDecay L s p.2

/-- `ρ̂_{jk} = ∫ ρ φ_{jk}` -/
def sqCoef (a L : ℝ) (ρ : ℂ → ℝ) (p : ℕ × ℕ) : ℝ := ∫ z, ρ z * sqMode a L p z

lemma abs_mul_le_one_of {u v : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1) : |u * v| ≤ 1 := by
  rw [abs_mul]; nlinarith [abs_nonneg u, abs_nonneg v]

lemma continuous_sqMode (a L : ℝ) (p : ℕ × ℕ) : Continuous (sqMode a L p) := by
  unfold sqMode sinMode; fun_prop

lemma abs_sqMode_le (a L : ℝ) (p : ℕ × ℕ) (z : ℂ) : |sqMode a L p z| ≤ 1 := by
  unfold sqMode; exact abs_mul_le_one_of (abs_sinMode_le _ _ _ _) (abs_sinMode_le _ _ _ _)

lemma sqDecay_pos (L s : ℝ) (p : ℕ × ℕ) : 0 < sqDecay L s p :=
  mul_pos (modeDecay_pos _ _ _) (modeDecay_pos _ _ _)

lemma summable_sqDecay {L s : ℝ} (hs : 0 < s) (hL : 0 < L) : Summable (sqDecay L s) :=
  (summable_modeDecay hs hL).mul_of_nonneg (summable_modeDecay hs hL)
    (fun _ => (modeDecay_pos _ _ _).le) (fun _ => (modeDecay_pos _ _ _).le)

/-- **Eigenfunction expansion of the square kernel.** -/
theorem hasSum_sqDirKernel_sine {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (x y : ℂ) :
    HasSum (fun p : ℕ × ℕ => 4 / L ^ 2 * sqDecay L s p * (sqMode a L p x * sqMode a L p y))
      (sqDirKernel a L s x y) := by
  have h1 := hasSum_intervalDirKernel_sine (a := a) hs hL x.re y.re
  have h2 := hasSum_intervalDirKernel_sine (a := a) hs hL x.im y.im
  have hsum : Summable fun p : ℕ × ℕ =>
      (2 / L * (modeDecay L s p.1 * (sinMode a L p.1 x.re * sinMode a L p.1 y.re))) *
      (2 / L * (modeDecay L s p.2 * (sinMode a L p.2 x.im * sinMode a L p.2 y.im))) := by
    refine ((summable_sqDecay hs hL).mul_left (4 / L ^ 2)).of_norm_bounded fun p => ?_
    have hb : ∀ (k : ℕ) (u v : ℝ),
        |2 / L * (modeDecay L s k * (sinMode a L k u * sinMode a L k v))| ≤
          2 / L * modeDecay L s k := fun k u v => by
      rw [abs_mul, abs_mul, abs_of_pos (modeDecay_pos _ _ _),
        abs_of_pos (by positivity : (0:ℝ) < 2 / L)]
      refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (modeDecay_pos _ _ _).le ?_)
        (by positivity)
      exact abs_mul_le_one_of (abs_sinMode_le _ _ _ _) (abs_sinMode_le _ _ _ _)
    rw [Real.norm_eq_abs, abs_mul]
    calc _ ≤ 2 / L * modeDecay L s p.1 * (2 / L * modeDecay L s p.2) :=
          mul_le_mul (hb _ _ _) (hb _ _ _) (abs_nonneg _)
            (mul_nonneg (by positivity) (modeDecay_pos _ _ _).le)
      _ = 4 / L ^ 2 * sqDecay L s p := by unfold sqDecay; field_simp; ring
  have h := h1.mul h2 hsum
  unfold sqDirKernel
  refine h.congr_fun fun p => ?_
  unfold sqDecay sqMode; field_simp; ring

lemma abs_sqDirKernel_term_le (a L s : ℝ) (hL : 0 < L) (p : ℕ × ℕ) (x y : ℂ) :
    |4 / L ^ 2 * sqDecay L s p * (sqMode a L p x * sqMode a L p y)| ≤ 4 / L ^ 2 * sqDecay L s p := by
  rw [abs_mul, abs_of_pos (by have := sqDecay_pos L s p; positivity)]
  refine mul_le_of_le_one_right (by have := sqDecay_pos L s p; positivity) ?_
  exact abs_mul_le_one_of (abs_sqMode_le _ _ _ _) (abs_sqMode_le _ _ _ _)

/-- dominated convergence for series with a product bound -/
lemma hasSum_integral_of_le_mul {ι : Type*} [Countable ι] {F : ι → ℂ → ℝ} {G g : ℂ → ℝ}
    {c : ι → ℝ} (hc : Summable c) (hg : Integrable g) (hF : ∀ p, AEStronglyMeasurable (F p))
    (hb : ∀ p z, |F p z| ≤ c p * |g z|) (hsum : ∀ z, HasSum (fun p => F p z) (G z)) :
    HasSum (fun p => ∫ z, F p z) (∫ z, G z) := by
  refine hasSum_integral_of_dominated_convergence (fun p z => c p * |g z|) hF
    (fun p => ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb p z)
    (ae_of_all _ fun z => hc.mul_right _) ?_ (ae_of_all _ hsum)
  simp_rw [tsum_mul_right]
  exact hg.abs.const_mul _

lemma abs_sqCoef_le {a L : ℝ} {ρ : ℂ → ℝ} (hρ : Integrable ρ) (p : ℕ × ℕ) :
    |sqCoef a L ρ p| ≤ ∫ z, |ρ z| := by
  unfold sqCoef
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (ae_of_all _ fun z => abs_nonneg _) hρ.abs (ae_of_all _ fun z => ?_))
  change |ρ z * sqMode a L p z| ≤ |ρ z|
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_sqMode_le _ _ _ _)

/-- **Spectral form of the kernel pairing.** -/
theorem hasSum_integral_sqDirKernel {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) {ρ σ : ℂ → ℝ}
    (hρ : Integrable ρ) (hσ : Integrable σ) :
    HasSum (fun p => 4 / L ^ 2 * sqDecay L s p * (sqCoef a L ρ p * sqCoef a L σ p))
      (∫ x, ∫ y, ρ x * sqDirKernel a L s x y * σ y) := by
  have hK := summable_sqDecay hs hL
  have hin : ∀ x, HasSum
      (fun p => ρ x * (4 / L ^ 2 * sqDecay L s p * sqMode a L p x) * sqCoef a L σ p)
      (∫ y, ρ x * sqDirKernel a L s x y * σ y) := by
    intro x
    have h := hasSum_integral_of_le_mul
      (F := fun p y => ρ x * (4 / L ^ 2 * sqDecay L s p * sqMode a L p x) *
        (σ y * sqMode a L p y))
      (G := fun y => ρ x * sqDirKernel a L s x y * σ y) (g := σ)
      (c := fun p => |ρ x| * (4 / L ^ 2 * sqDecay L s p))
      ((hK.mul_left _).mul_left _) hσ
      (fun p => (hσ.1.mul (continuous_sqMode a L p).aestronglyMeasurable).const_mul _)
      (fun p y => ?_) (fun y => ?_)
    · convert h using 1
      funext p; rw [sqCoef, integral_const_mul]
    · calc _ = |ρ x| * |4 / L ^ 2 * sqDecay L s p * (sqMode a L p x * sqMode a L p y)| *
            |σ y| := by rw [← abs_mul, ← abs_mul]; congr 1; ring
        _ ≤ |ρ x| * (4 / L ^ 2 * sqDecay L s p) * |σ y| := by
          gcongr; exact abs_sqDirKernel_term_le a L s hL p x y
    · exact (((hasSum_sqDirKernel_sine (a := a) hs hL x y).mul_left (ρ x)).mul_right
        (σ y)).congr_fun fun p => by ring
  have h := hasSum_integral_of_le_mul
    (F := fun p x => ρ x * (4 / L ^ 2 * sqDecay L s p * sqMode a L p x) * sqCoef a L σ p)
    (G := fun x => ∫ y, ρ x * sqDirKernel a L s x y * σ y) (g := ρ)
    (c := fun p => 4 / L ^ 2 * sqDecay L s p * ∫ z, |σ z|)
    ((hK.mul_left _).mul_right _) hρ
    (fun p => ((hρ.1.mul ((continuous_sqMode a L p).aestronglyMeasurable.const_mul _)).mul_const
      _)) (fun p x => ?_) hin
  · convert h using 1
    funext p
    rw [show (fun x => ρ x * (4 / L ^ 2 * sqDecay L s p * sqMode a L p x) * sqCoef a L σ p) =
      fun x => (4 / L ^ 2 * sqDecay L s p * sqCoef a L σ p) * (ρ x * sqMode a L p x) by
        funext x; ring, integral_const_mul, sqCoef]
    ring
  · have h1 := abs_sqCoef_le (a := a) (L := L) hσ p
    have h2 := abs_sqMode_le a L p x
    have hD : 0 ≤ 4 / L ^ 2 * sqDecay L s p := by have := sqDecay_pos L s p; positivity
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hD]
    calc |ρ x| * (4 / L ^ 2 * sqDecay L s p * |sqMode a L p x|) * |sqCoef a L σ p|
        ≤ |ρ x| * (4 / L ^ 2 * sqDecay L s p * 1) * ∫ z, |σ z| := by gcongr
      _ = _ := by ring

lemma volume_sqOpen_ne_top (a L : ℝ) : volume (sqOpen a L) ≠ ⊤ := by
  rw [sqOpen_eq_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

lemma integrable_of_bdd_sq {a L : ℝ} {ρ : ℂ → ℝ} (hρm : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) : Integrable ρ := by
  have hg : Integrable ((sqOpen a L).indicator fun _ => C) :=
    (integrableOn_const (volume_sqOpen_ne_top a L)).integrable_indicator
      (measurableSet_sqOpen a L)
  refine hg.mono' hρm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ sqOpen a L
  · rw [indicator_of_mem hz, Real.norm_eq_abs]; exact hC z
  · rw [indicator_of_notMem hz, h0 z hz, norm_zero]

lemma abs_integral_sqDirKernel_mul_le {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) {ρ : ℂ → ℝ}
    {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) (x : ℂ) :
    |∫ y, sqDirKernel a L s x y * ρ y| ≤ 4 * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := norm_integral_le_lintegral_norm (μ := volume) fun y => sqDirKernel a L s x y * ρ y
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) ?_)
  calc ∫⁻ y, ENNReal.ofReal ‖sqDirKernel a L s x y * ρ y‖
      = ∫⁻ y, (sqOpen a L).indicator
          (fun y => ENNReal.ofReal ‖sqDirKernel a L s x y * ρ y‖) y := by
        congr 1; funext y
        by_cases hy : y ∈ sqOpen a L
        · rw [indicator_of_mem hy]
        · rw [indicator_of_notMem hy, h0 y hy, mul_zero, norm_zero, ENNReal.ofReal_zero]
    _ = ∫⁻ y in sqOpen a L, ENNReal.ofReal ‖sqDirKernel a L s x y * ρ y‖ :=
        lintegral_indicator (measurableSet_sqOpen a L) _
    _ ≤ ∫⁻ y in sqOpen a L, ENNReal.ofReal C * ENNReal.ofReal |sqDirKernel a L s x y| := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul hC0, Real.norm_eq_abs, abs_mul, mul_comm C]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hC y) (abs_nonneg _))
    _ = ENNReal.ofReal C * ∫⁻ y in sqOpen a L, ENNReal.ofReal |sqDirKernel a L s x y| :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * 4 := by gcongr; exact lintegral_abs_sqDirKernel_le hs hL x
    _ = ENNReal.ofReal (4 * C) := by
        rw [mul_comm, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

lemma abs_integral_integral_sqDirKernel_le {a L s : ℝ} (hs : 0 < s) (hL : 0 < L)
    {ρ : ℂ → ℝ} (hρ : Integrable ρ) {C : ℝ} (hC : ∀ z, |ρ z| ≤ C)
    (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) :
    |∫ x, ∫ y, ρ x * sqDirKernel a L s x y * ρ y| ≤ ∫ x, |ρ x| * (4 * C) := by
  have e : ∀ x, ∫ y, ρ x * sqDirKernel a L s x y * ρ y =
      ρ x * ∫ y, sqDirKernel a L s x y * ρ y := fun x => by
    rw [← integral_const_mul]; congr 1; funext y; ring
  simp_rw [e]
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hρ.abs.mul_const _) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_integral_sqDirKernel_mul_le hs hL hC h0 x)
    (abs_nonneg _)

/-- **Square-summability of the coefficients** of a bounded `ρ` vanishing off the square. -/
theorem summable_sqCoef_sq {a L : ℝ} (hL : 0 < L) {ρ : ℂ → ℝ} (hρm : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, ρ z = 0) :
    Summable fun p => sqCoef a L ρ p ^ 2 := by
  have hρ := integrable_of_bdd_sq hρm hC h0
  set M := ∫ x, |ρ x| * (4 * C)
  have key : ∀ F : Finset (ℕ × ℕ), ∑ p ∈ F, 4 / L ^ 2 * sqCoef a L ρ p ^ 2 ≤ M := by
    intro F
    have hc : Continuous fun s : ℝ =>
        ∑ p ∈ F, 4 / L ^ 2 * sqDecay L s p * (sqCoef a L ρ p * sqCoef a L ρ p) := by
      unfold sqDecay modeDecay; fun_prop
    have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have e0 : (∑ p ∈ F, 4 / L ^ 2 * sqDecay L 0 p * (sqCoef a L ρ p * sqCoef a L ρ p)) =
        ∑ p ∈ F, 4 / L ^ 2 * sqCoef a L ρ p ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [sqDecay, modeDecay, mul_zero, zero_mul, Real.exp_zero]; ring
    rw [e0] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    refine (sum_le_hasSum F (fun p _ => ?_) (hasSum_integral_sqDirKernel (a := a) hs hL hρ hρ)).trans
      ((le_abs_self _).trans (abs_integral_integral_sqDirKernel_le hs hL hρ hC h0))
    have := sqDecay_pos L s p
    rw [← sq]; positivity
  have hs := summable_of_sum_le (fun p => by positivity) key
  refine (hs.mul_left (L ^ 2 / 4)).congr fun p => ?_
  field_simp

end HeatSq
end LQGMetric
