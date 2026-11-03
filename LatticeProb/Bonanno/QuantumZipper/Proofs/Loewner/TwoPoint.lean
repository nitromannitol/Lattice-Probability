/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.TwoPoint at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseHolo
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseFlow
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The deterministic reverse-Loewner two-point identity and its consequences

Task L2PT (`audits/2026-09-27-regcoord/AUDIT3.md` §1.3 and §4.2). Throughout, `W` is
continuous, `T ≥ 0` and `f = revMap W T`.

**(1) Identities.**
* `revMap_sub_revMap_eq` (in `ReverseHolo.lean`):
  `f z − f w = (z − w)·exp ∫₀ᵀ 2/(u^z u^w)`; the driver cancels.
* `log_im_revMap`: `log Im f z = log Im z + ∫₀ᵀ 2/|u^z_s|² ds` (that is,
  `d log Im u = 2/|u|² dt`); `im_revMap_eq`: `Im f z = Im z · exp (logImGain W T z)`.

**(2) Bounds.**
* `twoPoint_lower_sq`, `twoPoint_upper_sq` and their square-root forms `twoPoint_lower`,
  `twoPoint_upper`:
  `‖z−w‖·√(Im z Im w/(Im f z Im f w)) ≤ ‖f z − f w‖ ≤ ‖z−w‖·√(Im f z Im f w/(Im z Im w))`.
* `le_norm_deriv_revMap`, `norm_deriv_revMap_le`: `Im z/Im f z ≤ ‖f' z‖ ≤ Im f z/Im z`.
* `im_revMap_sq_le`: `(Im f z)² ≤ (Im z)² + 4T`.
* Composition: `TwoPointBounded.comp`, `revMap_concat_eq` (`revMap` of a concatenated driver is
  the composition, as in `Semigroup.revMap_split`), `twoPointBounded_concat`,
  `im_revMap_concat_sq_le`.

**(3) Folded circles** `σ = foldedCircle w r`, `r > 0`, with constants depending only on
`r₀ ≤ r` and `R ≥ ‖w‖ + r` (hence uniform over compact families of `(w, r)` with `r > 0`).
* (F) `isFrostman_revMap_foldedCircle`: `σ.map f` is `IsFrostman` with exponent `1/3`
  (uniformly, including circles tangent to or crossing `ℝ`), constant
  `18/√r₀ + 12·√(R²+4T)/r₀`. Proof: split the circle parameter into `{|Im| < τ}`
  (Lebesgue measure `≤ 36π√(τ/r)`, `volume_strip_le`) and its complement, whose image in a
  ball of radius `s` lies in two arcs of chord `≤ 2s√(R²+4T)/τ` (`twoPoint_lower_sq`,
  `volume_arc_le`); take `τ = s^{2/3}`.
* (L) `abs_log_norm_deriv_revMap_le`: `|log ‖f' u‖| ≤ |log √(R²+4T)| + |log Im u|` for
  `u ∈ H`, `Im u ≤ R`; `integrable_log_im_foldedCircle`,
  `integrable_log_norm_deriv_revMap_foldedCircle`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace TwoPoint

/-- The Frostman condition of `AUDIT3.md` §4 (notation for proof files). -/
def IsFrostman (ν : Measure ℂ) (α C : ℝ) : Prop :=
  ∀ w : ℂ, ∀ r : ℝ, 0 < r → (ν (Metric.closedBall w r)).toReal ≤ C * r ^ α

variable {W : ℝ → ℝ}

/-! ## (1) The logarithmic derivative of `Im u` -/

private lemma icc_mem_nhdsWithin_Ici₂ {a b t : ℝ} (ht1 : a ≤ t) (ht2 : t < b) :
    Set.Icc a b ∈ 𝓝[Set.Ici t] t := by
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio b, isOpen_Iio, ht2, fun x hx => ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici] at hx
  exact ⟨le_trans ht1 hx.2, le_of_lt hx.1⟩

theorem im_neg_two_div (u : ℂ) : (-2 / u).im = 2 * u.im / ‖u‖ ^ 2 := by
  have h1 : ((-2 : ℂ) * u⁻¹).im = (-2) * u⁻¹.im := by simp [Complex.mul_im]
  rw [show (-2 : ℂ) / u = (-2 : ℂ) * u⁻¹ from div_eq_mul_inv _ _, h1, Complex.inv_im,
    Complex.sq_norm]
  ring

theorem hasDerivWithinAt_im_of_isReverseSol {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (h : IsReverseSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => (u s).im) (2 * (u t).im / ‖u t‖ ^ 2) (Icc 0 T) t := by
  have hd := isReverseSol_hasDerivWithinAt W z T h ht
  have hc := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have e : (fun s => (u s).im) = Complex.imCLM ∘ fun s => u s + (W s : ℂ) := by
    funext s; simp
  rw [e, ← im_neg_two_div]
  exact hc.congr_deriv (Complex.imCLM_apply _)

/-- The gain `∫₀ᵀ 2/|u^z_s|² ds = log (Im f z / Im z)`. -/
def logImGain (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..T, 2 / ‖revMap W s z‖ ^ 2

theorem intervalIntegrable_gain (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {T : ℝ}
    (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => 2 / ‖revMap W s z‖ ^ 2) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hT]
  exact continuousOn_const.div ((continuousOn_revMap_time W hW hz hT).norm.pow 2)
    fun s hs => pow_ne_zero 2 (norm_ne_zero_iff.2 (revMap_ne_zero_of_im hW hz hs.1))

/-- **`d log Im u = 2/|u|² dt`.** -/
theorem log_im_revMap (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    Real.log (revMap W T z).im = Real.log z.im + logImGain W T z := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT
  have hE : EqOn (fun s => revMap W s z) u (Icc 0 T) :=
    fun s hs => revMap_eq W hW z hs.1 hs.2 hu
  have hpos : ∀ s ∈ Icc (0 : ℝ) T, 0 < (u s).im := fun s hs => (hu.2 s hs).1
  have hne : ∀ s ∈ Icc (0 : ℝ) T, u s ≠ 0 := fun s hs h0 => by
    have := hpos s hs; rw [h0] at this; simp at this
  set a : ℝ → ℝ := fun s => 2 / ‖u s‖ ^ 2 with ha
  have hacont : ContinuousOn a (Icc 0 T) :=
    continuousOn_const.div (hu.1.norm.pow 2) fun s hs =>
      pow_ne_zero 2 (norm_ne_zero_iff.2 (hne s hs))
  set A : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s with hA
  have hAder : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt A (a t) (Icc 0 T) t := by
    intro t ht
    have : Fact (t ∈ Set.Icc (0 : ℝ) T) := ⟨ht⟩
    have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc_right ht.2
    exact intervalIntegral.integral_hasDerivWithinAt_right
      ((hacont.mono hsub).intervalIntegrable)
      (hacont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hacont t ht)
  set E : ℝ → ℝ := fun t => Real.log (u t).im - A t with hEdef
  have hEder : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt E 0 (Icc 0 T) t := by
    intro t ht
    have h1 := ((hasDerivWithinAt_im_of_isReverseSol hu ht).log (hpos t ht).ne').sub
      (hAder t ht)
    refine h1.congr_deriv ?_
    have hn : ‖u t‖ ≠ 0 := norm_ne_zero_iff.2 (hne t ht)
    have hp := (hpos t ht).ne'
    simp only [ha]
    field_simp
    ring
  have hconst := constant_of_has_deriv_right_zero
    (fun t ht => (hEder t ht).continuousWithinAt)
    (fun t ht => (hEder t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (icc_mem_nhdsWithin_Ici₂ ht.1 ht.2)) T ⟨hT, le_rfl⟩
  have hu0im : (u 0).im = z.im := by rw [(hu.2 0 ⟨le_rfl, hT⟩).2]; simp
  have e0 : E 0 = Real.log z.im := by simp [hEdef, hA, hu0im]
  have eT : E T = Real.log (u T).im - A T := rfl
  have hint : logImGain W T z = A T := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    simp only [ha, hE hs]
  have hTT : revMap W T z = u T := hE ⟨hT, le_rfl⟩
  rw [hint, hTT]
  linarith [hconst, e0, eT]

theorem im_revMap_eq (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    (revMap W T z).im = z.im * Real.exp (logImGain W T z) := by
  have h1 : 0 < (revMap W T z).im := lt_of_lt_of_le hz (im_le_im_revMap W hW z hz hT)
  have hz' : 0 < z.im := hz
  rw [← Real.exp_log h1, log_im_revMap hW hz hT, Real.exp_add, Real.exp_log hz']

/-! ## (2) Bounds -/

theorem norm_two_div_mul_le (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖(2 : ℂ) / (a * b)‖ ≤ 1 / ‖a‖ ^ 2 + 1 / ‖b‖ ^ 2 := by
  rw [norm_div, norm_mul, Complex.norm_two]
  have ha' : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hb' : 0 < ‖b‖ := norm_pos_iff.2 hb
  rw [div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_pos ha' hb').le (sq_nonneg (‖a‖ - ‖b‖))]

theorem norm_integral_two_div_le (hW : Continuous W) {z w : ℂ} (hz : z ∈ H) (hw : w ∈ H)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ s in (0 : ℝ)..T, 2 / (revMap W s w * revMap W s z)‖ ≤
      (logImGain W T w + logImGain W T z) / 2 := by
  refine (intervalIntegral.norm_integral_le_integral_norm hT).trans ?_
  have hi1 := intervalIntegrable_gain hW hw hT
  have hi2 := intervalIntegrable_gain hW hz hT
  rw [logImGain, logImGain, ← intervalIntegral.integral_add hi1 hi2,
    ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_mono_on hT
    (intervalIntegrable_revMap_prod W hW hz hw hT).norm ((hi1.add hi2).div_const 2)
    fun s hs => ?_
  refine (norm_two_div_mul_le _ _ (revMap_ne_zero_of_im hW hw hs.1)
    (revMap_ne_zero_of_im hW hz hs.1)).trans (le_of_eq ?_)
  ring

theorem norm_revMap_sub_eq (hW : Continuous W) {z w : ℂ} (hz : z ∈ H) (hw : w ∈ H)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖revMap W T z - revMap W T w‖ =
      ‖z - w‖ * Real.exp (∫ s in (0 : ℝ)..T, 2 / (revMap W s z * revMap W s w)).re := by
  rw [revMap_sub_revMap_eq W hW hw hz hT, norm_mul, Complex.norm_exp]

/-- Lower two-point bound, squared form. -/
theorem twoPoint_lower_sq (hW : Continuous W) {z w : ℂ} (hz : z ∈ H) (hw : w ∈ H)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖z - w‖ ^ 2 * (z.im * w.im) ≤
      ‖revMap W T z - revMap W T w‖ ^ 2 * ((revMap W T z).im * (revMap W T w).im) := by
  rw [norm_revMap_sub_eq hW hz hw hT, im_revMap_eq hW hz hT, im_revMap_eq hW hw hT]
  set ρ := (∫ s in (0 : ℝ)..T, 2 / (revMap W s z * revMap W s w)).re
  have hρ : |ρ| ≤ (logImGain W T z + logImGain W T w) / 2 :=
    (Complex.abs_re_le_norm _).trans (norm_integral_two_div_le hW hw hz hT)
  have e2 : 1 ≤ Real.exp ρ ^ 2 * (Real.exp (logImGain W T z) * Real.exp (logImGain W T w)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.one_le_exp (by linarith [(abs_le.1 hρ).1])
  have hzw : 0 ≤ ‖z - w‖ ^ 2 * (z.im * w.im) :=
    mul_nonneg (sq_nonneg _) (mul_pos (show 0 < z.im from hz) (show 0 < w.im from hw)).le
  calc ‖z - w‖ ^ 2 * (z.im * w.im) = ‖z - w‖ ^ 2 * (z.im * w.im) * 1 := by ring
    _ ≤ ‖z - w‖ ^ 2 * (z.im * w.im) *
        (Real.exp ρ ^ 2 * (Real.exp (logImGain W T z) * Real.exp (logImGain W T w))) :=
      mul_le_mul_of_nonneg_left e2 hzw
    _ = _ := by ring

/-- Upper two-point bound, squared form. -/
theorem twoPoint_upper_sq (hW : Continuous W) {z w : ℂ} (hz : z ∈ H) (hw : w ∈ H)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖revMap W T z - revMap W T w‖ ^ 2 * (z.im * w.im) ≤
      ‖z - w‖ ^ 2 * ((revMap W T z).im * (revMap W T w).im) := by
  rw [norm_revMap_sub_eq hW hz hw hT, im_revMap_eq hW hz hT, im_revMap_eq hW hw hT]
  set ρ := (∫ s in (0 : ℝ)..T, 2 / (revMap W s z * revMap W s w)).re
  have hρ : |ρ| ≤ (logImGain W T z + logImGain W T w) / 2 :=
    (Complex.abs_re_le_norm _).trans (norm_integral_two_div_le hW hw hz hT)
  have e1 : Real.exp ρ ^ 2 ≤ Real.exp (logImGain W T z) * Real.exp (logImGain W T w) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 hρ).2])
  have hzw : 0 ≤ ‖z - w‖ ^ 2 * (z.im * w.im) :=
    mul_nonneg (sq_nonneg _) (mul_pos (show 0 < z.im from hz) (show 0 < w.im from hw)).le
  calc (‖z - w‖ * Real.exp ρ) ^ 2 * (z.im * w.im)
        = ‖z - w‖ ^ 2 * (z.im * w.im) * Real.exp ρ ^ 2 := by ring
    _ ≤ ‖z - w‖ ^ 2 * (z.im * w.im) *
        (Real.exp (logImGain W T z) * Real.exp (logImGain W T w)) :=
      mul_le_mul_of_nonneg_left e1 hzw
    _ = _ := by ring

theorem im_revMap_pos (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    0 < (revMap W T z).im :=
  lt_of_lt_of_le hz (im_le_im_revMap W hW z hz hT)

/-- **Lower two-point bound.** -/
theorem twoPoint_lower (hW : Continuous W) {z w : ℂ} (hz : z ∈ H) (hw : w ∈ H)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖z - w‖ * Real.sqrt (z.im * w.im / ((revMap W T z).im * (revMap W T w).im)) ≤
      ‖revMap W T z - revMap W T w‖ := by
  have hb := mul_pos (im_revMap_pos hW hz hT) (im_revMap_pos hW hw hT)
  have key : ‖z - w‖ ^ 2 * (z.im * w.im / ((revMap W T z).im * (revMap W T w).im)) ≤
      ‖revMap W T z - revMap W T w‖ ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hb]; exact twoPoint_lower_sq hW hz hw hT
  calc _ = Real.sqrt (‖z - w‖ ^ 2 *
        (z.im * w.im / ((revMap W T z).im * (revMap W T w).im))) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (‖revMap W T z - revMap W T w‖ ^ 2) := Real.sqrt_le_sqrt key
    _ = _ := Real.sqrt_sq (norm_nonneg _)

theorem abs_re_integral_sq_le (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ s in (0 : ℝ)..T, 2 / (revMap W s z) ^ 2).re| ≤ logImGain W T z := by
  refine (Complex.abs_re_le_norm _).trans ?_
  have h := norm_integral_two_div_le hW hz hz hT
  simp only [← sq] at h
  linarith

/-- **Derivative upper bound** `‖f' z‖ ≤ Im f z / Im z`. -/
theorem norm_deriv_revMap_le (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    ‖deriv (revMap W T) z‖ ≤ (revMap W T z).im / z.im := by
  have hz' : 0 < z.im := hz
  rw [deriv_revMap W hW hT hz, Complex.norm_exp, im_revMap_eq hW hz hT,
    mul_div_cancel_left₀ _ hz'.ne']
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (abs_re_integral_sq_le hW hz hT))

/-- **Derivative lower bound** `Im z / Im f z ≤ ‖f' z‖`. -/
theorem le_norm_deriv_revMap (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    z.im / (revMap W T z).im ≤ ‖deriv (revMap W T) z‖ := by
  have hz' : 0 < z.im := hz
  rw [deriv_revMap W hW hT hz, Complex.norm_exp, im_revMap_eq hW hz hT,
    show z.im / (z.im * Real.exp (logImGain W T z)) = Real.exp (-logImGain W T z) by
      rw [Real.exp_neg]; field_simp]
  exact Real.exp_le_exp.2 (by linarith [neg_abs_le (∫ s in (0 : ℝ)..T,
    2 / (revMap W s z) ^ 2).re, abs_re_integral_sq_le hW hz hT])

/-- **`(Im f z)² ≤ (Im z)² + 4T`.** -/
theorem im_revMap_sq_le (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {T : ℝ} (hT : 0 ≤ T) :
    (revMap W T z).im ^ 2 ≤ z.im ^ 2 + 4 * T := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz T hT
  rw [revMap_eq W hW z hT le_rfl hu]
  have hpos : ∀ s ∈ Icc (0 : ℝ) T, 0 < (u s).im := fun s hs => (hu.2 s hs).1
  have hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun t => 4 * t - (u t).im ^ 2)
      (4 - 4 * (u t).im ^ 2 / ‖u t‖ ^ 2) (Icc 0 T) t := by
    intro t ht
    have h1 := ((hasDerivWithinAt_id t (Icc (0 : ℝ) T)).const_mul 4).sub
      ((hasDerivWithinAt_im_of_isReverseSol hu ht).pow 2)
    refine h1.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have hmono : MonotoneOn (fun t => 4 * t - (u t).im ^ 2) (Icc 0 T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => 4 - 4 * (u t).im ^ 2 / ‖u t‖ ^ 2) (convex_Icc 0 T)
      (fun t ht => (hd t ht).continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Icc] at ht
      exact (hd t (Ioo_subset_Icc_self ht)).mono (by rw [interior_Icc]; exact Ioo_subset_Icc_self)
    · rw [interior_Icc] at ht
      have hne : 0 < ‖u t‖ := lt_of_lt_of_le (hpos t (Ioo_subset_Icc_self ht))
        ((le_abs_self _).trans (Complex.abs_im_le_norm _))
      have h2 : (u t).im ^ 2 ≤ ‖u t‖ ^ 2 := by
        have := Complex.abs_im_le_norm (u t)
        nlinarith [abs_nonneg (u t).im, sq_abs (u t).im]
      have : 4 * (u t).im ^ 2 / ‖u t‖ ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
  have h := hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  have hu0im : (u 0).im = z.im := by rw [(hu.2 0 ⟨le_rfl, hT⟩).2]; simp
  simp only [hu0im, mul_zero, zero_sub] at h
  linarith

/-! ### Composition along concatenated drivers -/

/-- The two-point bounds (squared forms), as a property of a map `H → H`. -/
def TwoPointBounded (f : ℂ → ℂ) : Prop :=
  MapsTo f H H ∧ ∀ z ∈ H, ∀ w ∈ H,
    ‖z - w‖ ^ 2 * (z.im * w.im) ≤ ‖f z - f w‖ ^ 2 * ((f z).im * (f w).im) ∧
    ‖f z - f w‖ ^ 2 * (z.im * w.im) ≤ ‖z - w‖ ^ 2 * ((f z).im * (f w).im)

/-- The two-point bounds compose. -/
theorem TwoPointBounded.comp {f g : ℂ → ℂ} (hg : TwoPointBounded g) (hf : TwoPointBounded f) :
    TwoPointBounded (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, fun z hz w hw => ?_⟩
  have hfz := hf.1 hz
  have hfw := hf.1 hw
  have ha : 0 < z.im * w.im := mul_pos hz hw
  have hb : 0 < (f z).im * (f w).im := mul_pos hfz hfw
  have hc : 0 < (g (f z)).im * (g (f w)).im := mul_pos (hg.1 hfz) (hg.1 hfw)
  obtain ⟨l1, u1⟩ := hf.2 z hz w hw
  obtain ⟨l2, u2⟩ := hg.2 _ hfz _ hfw
  simp only [Function.comp]
  refine ⟨l1.trans l2, ?_⟩
  have e1 := mul_le_mul_of_nonneg_left u2 ha.le
  have e2 := mul_le_mul_of_nonneg_left u1 hc.le
  refine le_of_mul_le_mul_right ?_ hb
  nlinarith [e1, e2]

/-- `revMap` of a concatenated driver is the composition (cf. `Semigroup.revMap_split`). -/
theorem revMap_concat_eq (hW : Continuous W) {W1 W2 : ℝ → ℝ} {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) (h1 : EqOn W W1 (Icc 0 t)) (h2 : ∀ r ∈ Icc (0 : ℝ) s, W (t + r) - W t = W2 r)
    {z : ℂ} (hz : z ∈ H) :
    revMap W (t + s) z = revMap W2 s (revMap W1 t z) := by
  rw [ReverseFlow.revMap_add W hW z hz ht hs, ReverseFlow.revMap_congr_drive z h1]
  exact ReverseFlow.revMap_congr_drive _ fun u hu => h2 u hu

/-! ## (3) Folded circles -/

section Circles

theorem abs_le_of_abs_sin_le {x ε : ℝ} (hx : |x| ≤ π / 2) (h : |Real.sin x| ≤ ε) :
    |x| ≤ π / 2 * ε := by
  have hπ := Real.pi_pos
  have key : 2 / π * |x| ≤ |Real.sin x| := by
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0]
      exact (Real.mul_le_sin h0 (by linarith [(abs_le.1 hx).2])).trans (le_abs_self _)
    · rw [abs_of_nonpos h0]
      have := Real.mul_le_sin (neg_nonneg.2 h0) (by linarith [(abs_le.1 hx).1])
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have e : π / 2 * (2 / π * |x|) = |x| := by field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left (key.trans h) (by positivity)

theorem norm_circleMap_sub_circleMap (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ θ₀ : ℝ) :
    ‖circleMap z r θ - circleMap z r θ₀‖ = r * |2 * Real.sin ((θ - θ₀) / 2)| := by
  have e : circleMap z r θ - circleMap z r θ₀ =
      ((r : ℂ) * Complex.exp (θ₀ * I)) * (Complex.exp (I * ((θ - θ₀ : ℝ) : ℂ)) - 1) := by
    simp only [circleMap]
    rw [show (θ : ℂ) * I = θ₀ * I + I * ((θ - θ₀ : ℝ) : ℂ) by push_cast; ring, Complex.exp_add]
    ring
  rw [e, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_nonneg hr, mul_one]

/-- Lebesgue measure of the parameters of an arc of the circle `∂B(z,r)` inside a ball of
radius `D`: at most `6πD/r`. -/
theorem volume_arc_le (z q : ℂ) {r : ℝ} (hr : 0 < r) (D : ℝ) :
    volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap z r θ - q‖ ≤ D} ≤
      ENNReal.ofReal (6 * π * D / r) := by
  set S := {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap z r θ - q‖ ≤ D}
  rcases S.eq_empty_or_nonempty with hS | ⟨θ₀, h0, hq0⟩
  · rw [hS, measure_empty]; exact zero_le
  have hπ := Real.pi_pos
  have hD : 0 ≤ D := (norm_nonneg _).trans hq0
  set δ := π * D / r with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hsub : S ⊆ Icc (θ₀ - δ) (θ₀ + δ) ∪ Icc (θ₀ + 2 * π - δ) (θ₀ + 2 * π + δ) ∪
      Icc (θ₀ - 2 * π - δ) (θ₀ - 2 * π + δ) := by
    rintro θ ⟨hθ, hθq⟩
    have hch : r * |2 * Real.sin ((θ - θ₀) / 2)| ≤ 2 * D := by
      rw [← norm_circleMap_sub_circleMap z hr.le]
      refine (norm_sub_le_norm_sub_add_norm_sub _ q _).trans ?_
      rw [norm_sub_rev q]; linarith
    have hsin : |Real.sin ((θ - θ₀) / 2)| ≤ D / r := by
      rw [abs_mul, abs_two] at hch
      rw [le_div_iff₀ hr]; linarith
    have hx1 : -π < (θ - θ₀) / 2 := by linarith [hθ.1, h0.2]
    have hx2 : (θ - θ₀) / 2 < π := by linarith [hθ.2, h0.1]
    rcases le_or_gt |(θ - θ₀) / 2| (π / 2) with hx | hx
    · have h := abs_le.1 (abs_le_of_abs_sin_le hx hsin)
      left; left
      constructor
      · rw [hδ]; linarith [h.1, show π * D / r = π * (D / r) by ring]
      · rw [hδ]; linarith [h.2, show π * D / r = π * (D / r) by ring]
    · rcases le_or_gt 0 ((θ - θ₀) / 2) with hx0 | hx0
      · rw [abs_of_nonneg hx0] at hx
        have hy : |(θ - θ₀) / 2 - π| ≤ π / 2 := abs_le.2 ⟨by linarith, by linarith⟩
        have hs' : |Real.sin ((θ - θ₀) / 2 - π)| ≤ D / r := by
          rw [Real.sin_sub_pi, abs_neg]; exact hsin
        have h := abs_le.1 (abs_le_of_abs_sin_le hy hs')
        left; right
        constructor
        · rw [hδ]; linarith [h.1, show π * D / r = π * (D / r) by ring]
        · rw [hδ]; linarith [h.2, show π * D / r = π * (D / r) by ring]
      · rw [abs_of_neg hx0] at hx
        have hy : |(θ - θ₀) / 2 + π| ≤ π / 2 := abs_le.2 ⟨by linarith, by linarith⟩
        have hs' : |Real.sin ((θ - θ₀) / 2 + π)| ≤ D / r := by
          rw [Real.sin_add_pi, abs_neg]; exact hsin
        have h := abs_le.1 (abs_le_of_abs_sin_le hy hs')
        right
        constructor
        · rw [hδ]; linarith [h.1, show π * D / r = π * (D / r) by ring]
        · rw [hδ]; linarith [h.2, show π * D / r = π * (D / r) by ring]
  have hI : ∀ c : ℝ, volume (Icc (c - δ) (c + δ)) = ENNReal.ofReal (2 * δ) := fun c => by
    rw [Real.volume_Icc]; ring_nf
  have h2 : (0 : ℝ) ≤ 2 * δ := by positivity
  have h3 : ENNReal.ofReal (2 * δ) + ENNReal.ofReal (2 * δ) + ENNReal.ofReal (2 * δ) =
      ENNReal.ofReal (6 * π * D / r) := by
    rw [← ENNReal.ofReal_add h2 h2, ← ENNReal.ofReal_add (add_nonneg h2 h2) h2]
    congr 1; rw [hδ]; ring
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
  rw [hI, hI, hI, h3]

theorem circleMap_re' (z : ℂ) (r θ : ℝ) : (circleMap z r θ).re = z.re + r * Real.cos θ := by
  simp [circleMap, Complex.exp_ofReal_mul_I_re]

theorem circleMap_im' (z : ℂ) (r θ : ℝ) : (circleMap z r θ).im = z.im + r * Real.sin θ := by
  simp [circleMap, Complex.exp_ofReal_mul_I_im]

/-- Lebesgue measure of the parameters of the part of the circle `∂B(z,r)` in the strip
`{|Im| < τ}`: at most `36π√(τ/r)`, uniformly in the centre (tangent circles included). -/
theorem volume_strip_le (z : ℂ) {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ) :
    volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap z r θ).im| < τ} ≤
      ENNReal.ofReal (36 * π * Real.sqrt (τ / r)) := by
  have hπ := Real.pi_pos
  set s := Real.sqrt (τ / r) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = τ / r := Real.sq_sqrt (by positivity)
  have hτs : τ = r * s ^ 2 := by rw [hs2]; field_simp
  rcases le_or_gt r τ with hrτ | hrτ
  · have h1 : 1 ≤ τ / r := (one_le_div hr).2 hrτ
    have hs1 : 1 ≤ s := by
      rw [hs, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
    refine (measure_mono (fun θ (hθ : θ ∈ {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧
      |(circleMap z r θ).im| < τ}) => hθ.1)).trans ?_
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hs1 : s ≤ 1 := by
    have h1 : τ / r ≤ 1 := (div_le_one hr).2 hrτ.le
    rw [hs, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
  set m := Real.sqrt (max (r ^ 2 - z.im ^ 2) 0) with hm
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hm2 : m ^ 2 = max (r ^ 2 - z.im ^ 2) 0 := Real.sq_sqrt (le_max_right _ _)
  have hsub : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap z r θ).im| < τ} ⊆
      {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap z r θ - ((z.re + m : ℝ) : ℂ)‖ ≤ 3 * r * s} ∪
      {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap z r θ - ((z.re - m : ℝ) : ℂ)‖ ≤ 3 * r * s} := by
    rintro θ ⟨hθ, hy⟩
    rw [circleMap_im'] at hy
    obtain ⟨c, hc⟩ : ∃ c, c = Real.cos θ := ⟨_, rfl⟩
    obtain ⟨sn, hsn⟩ : ∃ sn, sn = Real.sin θ := ⟨_, rfl⟩
    have hcs : sn ^ 2 + c ^ 2 = 1 := by rw [hc, hsn]; exact Real.sin_sq_add_cos_sq θ
    obtain ⟨y, hydef⟩ : ∃ y, y = z.im + r * sn := ⟨_, rfl⟩
    have hyτ : |y| < r * s ^ 2 := by rw [hydef, hsn, ← hτs]; exact hy
    have hsn1 : |sn| ≤ 1 := hsn ▸ Real.abs_sin_le_one θ
    have hysn : |y * sn| ≤ r * s ^ 2 := by
      rw [abs_mul]; nlinarith [abs_nonneg y, abs_nonneg sn]
    have hy2 : y ^ 2 ≤ r ^ 2 * s ^ 2 := by
      have : |y| ^ 2 ≤ (r * s ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hyτ.le 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg s, mul_pos hr hr]
    have hE : |y ^ 2 - 2 * y * r * sn| ≤ 3 * r ^ 2 * s ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left (abs_le.1 hysn).2 hr.le
      have a2 := mul_le_mul_of_nonneg_left (abs_le.1 hysn).1 hr.le
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg y]
    set v := |r * c| with hv
    have hv0 : 0 ≤ v := abs_nonneg _
    have hv2 : v ^ 2 = r ^ 2 * c ^ 2 := by rw [hv, sq_abs, mul_pow]
    have hb : z.im = y - r * sn := by rw [hydef]; ring
    have hvm : |v ^ 2 - m ^ 2| ≤ 3 * r ^ 2 * s ^ 2 := by
      rw [hv2, hm2]
      rcases le_total 0 (r ^ 2 - z.im ^ 2) with h | h
      · rw [max_eq_left h]
        have e : r ^ 2 * c ^ 2 - (r ^ 2 - z.im ^ 2) = y ^ 2 - 2 * y * r * sn := by
          rw [hb]; linear_combination (r ^ 2) * hcs
        rw [e]; exact hE
      · rw [max_eq_right h, sub_zero, abs_of_nonneg (by positivity)]
        have e : r ^ 2 * c ^ 2 = (r ^ 2 - z.im ^ 2) + (y ^ 2 - 2 * y * r * sn) := by
          rw [hb]; linear_combination (r ^ 2) * hcs
        linarith [(abs_le.1 hE).2]
    have hvm' : |v - m| ≤ 2 * r * s := by
      have e1 : v ^ 2 - m ^ 2 = (v - m) * (v + m) := by ring
      have h1 : (v - m) ^ 2 ≤ |v ^ 2 - m ^ 2| := by
        rw [e1, abs_mul, abs_of_nonneg (add_nonneg hv0 hm0), sq, ← abs_mul_abs_self (v - m)]
        exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith)
          (abs_nonneg _)
      have hrs : 0 ≤ r ^ 2 * s ^ 2 := by positivity
      have h2 : (v - m) ^ 2 ≤ (2 * r * s) ^ 2 := by
        have e2 : (2 * r * s) ^ 2 = 4 * (r ^ 2 * s ^ 2) := by ring
        rw [e2]; linarith
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt ((v - m) ^ 2) ≤ Real.sqrt ((2 * r * s) ^ 2) := Real.sqrt_le_sqrt h2
        _ = 2 * r * s := Real.sqrt_sq (by positivity)
    have hs2s : s ^ 2 ≤ s := by rw [sq]; exact mul_le_of_le_one_left hs0 hs1
    have hyrs : |y| ≤ r * s := by
      have := mul_le_mul_of_nonneg_left hs2s hr.le
      linarith [hyτ.le]
    have hre : ∀ P : ℝ, ‖circleMap z r θ - (P : ℂ)‖ ≤ |z.re + r * c - P| + |y| := by
      intro P
      refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
      rw [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, circleMap_re',
        circleMap_im', sub_zero, ← hc, ← hsn, ← hydef]
    rcases le_total 0 c with hc0 | hc0
    · left
      refine ⟨hθ, (hre _).trans ?_⟩
      have : z.re + r * c - (z.re + m) = v - m := by
        rw [hv, abs_of_nonneg (mul_nonneg hr.le hc0)]; ring
      rw [this]; linarith
    · right
      refine ⟨hθ, (hre _).trans ?_⟩
      have : z.re + r * c - (z.re - m) = -(v - m) := by
        rw [hv, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hr.le hc0)]; ring
      rw [this, abs_neg]; linarith
  have hA : (0 : ℝ) ≤ 6 * π * (3 * r * s) / r := by positivity
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (volume_arc_le _ _ hr _) (volume_arc_le _ _ hr _)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add hA hA]
  congr 1
  field_simp
  ring

theorem im_foldH (x : ℂ) : (foldH x).im = |x.im| := by
  unfold foldH
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · simp [abs_of_neg (not_le.1 h)]

theorem norm_foldH (x : ℂ) : ‖foldH x‖ = ‖x‖ := by
  unfold foldH
  split_ifs <;> simp

theorem foldH_near {x q : ℂ} {D : ℝ} (h : ‖foldH x - q‖ ≤ D) :
    ‖x - q‖ ≤ D ∨ ‖x - (starRingEnd ℂ) q‖ ≤ D := by
  unfold foldH at h
  split_ifs at h
  · exact Or.inl h
  · right
    have e : x - (starRingEnd ℂ) q = (starRingEnd ℂ) ((starRingEnd ℂ) x - q) := by simp
    rw [e, Complex.norm_conj]
    exact h

theorem norm_circleMap_le_add (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖circleMap z r θ‖ ≤ ‖z‖ + r := by
  simp only [circleMap]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_one]

private lemma revMap_of_not_mem' {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : ¬ 0 < z.im) :
    revMap W T z = 0 := by
  unfold revMap
  rw [dif_neg]
  rintro ⟨u, hu⟩
  obtain ⟨h1, h2⟩ := hu.2 0 ⟨le_rfl, hT⟩
  rw [h2, intervalIntegral.integral_same] at h1
  exact hz (by simpa using h1)

theorem measurable_revMap (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    Measurable (revMap W T) := by
  classical
  have e : revMap W T = H.piecewise (revMap W T) (fun _ => 0) := by
    funext z
    show revMap W T z = if z ∈ H then revMap W T z else 0
    by_cases hz : z ∈ H
    · rw [if_pos hz]
    · rw [if_neg hz]; exact revMap_of_not_mem' hT hz
  rw [e]
  exact ContinuousOn.measurable_piecewise (differentiableOn_revMap W hW hT).continuousOn
    continuousOn_const isOpen_H.measurableSet

theorem foldedCircle_map_apply {g : ℂ → ℂ} (hg : Measurable g) (w : ℂ) (r : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) :
    ((foldedCircle w r).map g) B = (ENNReal.ofReal (2 * π))⁻¹ *
      volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ g (foldH (circleMap w r θ)) ∈ B} := by
  rw [Measure.map_apply hg hB, foldedCircle, Measure.map_apply measurable_foldH (hg hB),
    circleUnif, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_circleMap w r) (measurable_foldH (hg hB)),
    Measure.restrict_apply' measurableSet_Ico]
  congr 2
  ext θ
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq]
  exact and_comm

theorem foldedCircle_apply' (w : ℂ) (r : ℝ) {B : Set ℂ} (hB : MeasurableSet B) :
    foldedCircle w r B = (ENNReal.ofReal (2 * π))⁻¹ *
      volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ foldH (circleMap w r θ) ∈ B} := by
  have := foldedCircle_map_apply measurable_id w r hB
  rwa [Measure.map_id] at this

/-- Two points of `H` above height `τ`, below height `R`, whose images lie in a common ball of
radius `s`, are within `2s√(R²+4T)/τ` of each other. -/
theorem norm_sub_mul_le_of_mem_ball (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {u v p : ℂ}
    {τ R s : ℝ} (hτ : 0 < τ) (hu : τ ≤ u.im) (hv : τ ≤ v.im) (huR : u.im ≤ R) (hvR : v.im ≤ R)
    (hfu : revMap W T u ∈ Metric.closedBall p s) (hfv : revMap W T v ∈ Metric.closedBall p s) :
    ‖u - v‖ * τ ≤ 2 * s * Real.sqrt (R ^ 2 + 4 * T) := by
  have hu0 : u ∈ H := show 0 < u.im by linarith
  have hv0 : v ∈ H := show 0 < v.im by linarith
  set M := Real.sqrt (R ^ 2 + 4 * T)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  rw [Metric.mem_closedBall, dist_eq_norm] at hfu hfv
  have hd : ‖revMap W T u - revMap W T v‖ ≤ 2 * s := by
    refine (norm_sub_le_norm_sub_add_norm_sub _ p _).trans ?_
    rw [norm_sub_rev p]; linarith
  have hs : 0 ≤ s := (norm_nonneg _).trans hfu
  have hfuM : (revMap W T u).im ≤ M := (le_abs_self _).trans
    (Real.abs_le_sqrt (by nlinarith [im_revMap_sq_le hW hu0 hT]))
  have hfvM : (revMap W T v).im ≤ M := (le_abs_self _).trans
    (Real.abs_le_sqrt (by nlinarith [im_revMap_sq_le hW hv0 hT]))
  have hImp : (revMap W T u).im * (revMap W T v).im ≤ M ^ 2 := by
    rw [sq]; exact mul_le_mul hfuM hfvM (im_revMap_pos hW hv0 hT).le hM
  have hsq : (‖u - v‖ * τ) ^ 2 ≤ (2 * s * M) ^ 2 := by
    calc (‖u - v‖ * τ) ^ 2 = ‖u - v‖ ^ 2 * (τ * τ) := by ring
      _ ≤ ‖u - v‖ ^ 2 * (u.im * v.im) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hu hv hτ.le (by linarith)) (sq_nonneg _)
      _ ≤ ‖revMap W T u - revMap W T v‖ ^ 2 *
          ((revMap W T u).im * (revMap W T v).im) := twoPoint_lower_sq hW hu0 hv0 hT
      _ ≤ (2 * s) ^ 2 * M ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hd 2) hImp
          (mul_nonneg (im_revMap_pos hW hu0 hT).le (im_revMap_pos hW hv0 hT).le) (by positivity)
      _ = (2 * s * M) ^ 2 := by ring
  have h1 : 0 ≤ ‖u - v‖ * τ := mul_nonneg (norm_nonneg _) hτ.le
  have h2 : 0 ≤ 2 * s * M := by positivity
  nlinarith [hsq, h1, h2]

/-- **(F) Frostman bound** for `f_* fc(w,r)`, `f = revMap W T`, with exponent `1/3`, uniformly
for `r ≥ r₀ > 0` and `‖w‖ + r ≤ R`. -/
theorem isFrostman_revMap_foldedCircle (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {w : ℂ}
    {r r₀ R : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hwR : ‖w‖ + r ≤ R) :
    IsFrostman ((foldedCircle w r).map (revMap W T)) (1 / 3)
      (18 / Real.sqrt r₀ + 12 * Real.sqrt (R ^ 2 + 4 * T) / r₀) := by
  intro p s hs
  have hπ := Real.pi_pos
  have hr0 : 0 < r := hr₀.trans_le hr
  set M := Real.sqrt (R ^ 2 + 4 * T) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  set t := s ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hs _
  have ht3 : t ^ 3 = s := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
  set τ := t ^ 2 with hτ
  have hτ0 : 0 < τ := by positivity
  set D := 2 * t * M with hD
  have hD0 : 0 ≤ D := by positivity
  set S := {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧
    revMap W T (foldH (circleMap w r θ)) ∈ Metric.closedBall p s}
  set Bad := {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap w r θ).im| < τ}
  set Good := {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ τ ≤ |(circleMap w r θ).im| ∧
    revMap W T (foldH (circleMap w r θ)) ∈ Metric.closedBall p s}
  have hSsub : S ⊆ Bad ∪ Good := by
    rintro θ ⟨h1, h2⟩
    rcases lt_or_ge |(circleMap w r θ).im| τ with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h1, h, h2⟩
  have hbound : ∀ θ, (foldH (circleMap w r θ)).im ≤ R := fun θ =>
    (Complex.im_le_norm _).trans ((norm_foldH _).le.trans
      ((norm_circleMap_le_add w hr0.le θ).trans hwR))
  have hGood : volume Good ≤
      ENNReal.ofReal (6 * π * D / r) + ENNReal.ofReal (6 * π * D / r) := by
    rcases Good.eq_empty_or_nonempty with hG | ⟨θ₀, h0, hτ0', hF0⟩
    · rw [hG, measure_empty]; exact zero_le
    set q := foldH (circleMap w r θ₀)
    have hsub : Good ⊆ {θ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap w r θ - q‖ ≤ D} ∪
        {θ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap w r θ - (starRingEnd ℂ) q‖ ≤ D} := by
      rintro θ ⟨h1, hτθ, hFθ⟩
      have hkey := norm_sub_mul_le_of_mem_ball hW hT hτ0
        (show τ ≤ (foldH (circleMap w r θ)).im by rw [im_foldH]; exact hτθ)
        (show τ ≤ q.im by rw [im_foldH]; exact hτ0') (hbound θ) (hbound θ₀) hFθ hF0
      have hclose : ‖foldH (circleMap w r θ) - q‖ ≤ D := by
        rw [← ht3] at hkey
        refine le_of_mul_le_mul_right ?_ hτ0
        calc ‖foldH (circleMap w r θ) - q‖ * τ ≤ 2 * t ^ 3 * M := hkey
          _ = D * τ := by rw [hD, hτ]; ring
      rcases foldH_near hclose with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h⟩
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add (volume_arc_le _ _ hr0 _) (volume_arc_le _ _ hr0 _)))
  have hBad : volume Bad ≤ ENNReal.ofReal (36 * π * Real.sqrt (τ / r)) :=
    volume_strip_le w hr0 hτ0
  have ha : (0 : ℝ) ≤ 36 * π * Real.sqrt (τ / r) := by positivity
  have hb : (0 : ℝ) ≤ 6 * π * D / r := by positivity
  have hvol : volume S ≤
      ENNReal.ofReal (36 * π * Real.sqrt (τ / r) + 2 * (6 * π * D / r)) := by
    refine (measure_mono hSsub).trans ((measure_union_le _ _).trans
      ((add_le_add hBad hGood).trans (le_of_eq ?_)))
    rw [← ENNReal.ofReal_add hb hb, ← ENNReal.ofReal_add ha (add_nonneg hb hb)]
    ring_nf
  have hν : ((foldedCircle w r).map (revMap W T)) (Metric.closedBall p s) ≤
      ENNReal.ofReal ((2 * π)⁻¹ * (36 * π * Real.sqrt (τ / r) + 2 * (6 * π * D / r))) := by
    rw [foldedCircle_map_apply (measurable_revMap hW hT) w r
      Metric.isClosed_closedBall.measurableSet,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹),
      ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    exact mul_le_mul' le_rfl hvol
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hν).trans ?_
  have hsq : Real.sqrt (τ / r) = t / Real.sqrt r := by
    rw [Real.sqrt_div (by positivity), hτ, Real.sqrt_sq ht0.le]
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hsr₀ : 0 < Real.sqrt r₀ := Real.sqrt_pos.2 hr₀
  have e : (2 * π)⁻¹ * (36 * π * Real.sqrt (τ / r) + 2 * (6 * π * D / r)) =
      18 * t / Real.sqrt r + 12 * M * t / r := by
    rw [hsq, hD]; field_simp; ring
  rw [e]
  have i1 : 18 * t / Real.sqrt r ≤ 18 * t / Real.sqrt r₀ :=
    div_le_div_of_nonneg_left (by positivity) hsr₀ (Real.sqrt_le_sqrt hr)
  have i2 : 12 * M * t / r ≤ 12 * M * t / r₀ :=
    div_le_div_of_nonneg_left (by positivity) hr₀ hr
  calc 18 * t / Real.sqrt r + 12 * M * t / r ≤ 18 * t / Real.sqrt r₀ + 12 * M * t / r₀ :=
        add_le_add i1 i2
    _ = (18 / Real.sqrt r₀ + 12 * M / r₀) * t := by ring

/-! ### (L) The logarithmic term -/

/-- **(L) pointwise.** `|log ‖f' u‖| ≤ |log √(R²+4T)| + |log Im u|` for `u ∈ H`, `Im u ≤ R`. -/
theorem abs_log_norm_deriv_revMap_le (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {u : ℂ}
    (hu : u ∈ H) {R : ℝ} (huR : u.im ≤ R) :
    |Real.log ‖deriv (revMap W T) u‖| ≤
      |Real.log (Real.sqrt (R ^ 2 + 4 * T))| + |Real.log u.im| := by
  have hu' : 0 < u.im := hu
  rw [log_norm_deriv_revMap W hW hT hu]
  refine (abs_re_integral_sq_le hW hu hT).trans ?_
  have hL := log_im_revMap hW hu hT
  have hfpos := im_revMap_pos hW hu hT
  have hle : (revMap W T u).im ≤ Real.sqrt (R ^ 2 + 4 * T) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [im_revMap_sq_le hW hu hT]))
  have := Real.log_le_log hfpos hle
  linarith [le_abs_self (Real.log (Real.sqrt (R ^ 2 + 4 * T))), neg_abs_le (Real.log u.im)]

theorem foldedCircle_strip_le (w : ℂ) {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ) :
    foldedCircle w r {x | |x.im| < τ} ≤ ENNReal.ofReal (18 * Real.sqrt (τ / r)) := by
  have hπ := Real.pi_pos
  have hB : MeasurableSet {x : ℂ | |x.im| < τ} :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).measurableSet
  rw [foldedCircle_apply' w r hB]
  simp only [mem_setOf_eq, im_foldH, abs_abs]
  calc (ENNReal.ofReal (2 * π))⁻¹ *
        volume {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap w r θ).im| < τ}
      ≤ (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (36 * π * Real.sqrt (τ / r)) :=
        mul_le_mul' le_rfl (volume_strip_le w hr hτ)
    _ = ENNReal.ofReal (18 * Real.sqrt (τ / r)) := by
        rw [← ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 * π),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹)]
        congr 1; field_simp; ring

theorem foldedCircle_im_nonpos (w : ℂ) {r : ℝ} (hr : 0 < r) :
    foldedCircle w r {x | x.im ≤ 0} = 0 := by
  have hB1 : MeasurableSet {x : ℂ | x.im ≤ 0} :=
    (isClosed_le Complex.continuous_im continuous_const).measurableSet
  have hmono : ∀ τ > 0, foldedCircle w r {x | x.im ≤ 0} ≤ foldedCircle w r {x | |x.im| < τ} := by
    intro τ hτ
    have hB2 : MeasurableSet {x : ℂ | |x.im| < τ} :=
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).measurableSet
    rw [foldedCircle_apply' w r hB1, foldedCircle_apply' w r hB2]
    refine mul_le_mul' le_rfl (measure_mono fun θ hθ => ⟨hθ.1, ?_⟩)
    have h1 := hθ.2
    simp only [mem_setOf_eq, im_foldH] at h1 ⊢
    rw [abs_abs]
    have := abs_nonneg (circleMap w r θ).im
    linarith
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (zero_le)
  rw [zero_add]
  have hε' : (0 : ℝ) < ε := hε
  refine (hmono (r * (ε / 18) ^ 2) (by positivity)).trans
    ((foldedCircle_strip_le w hr (by positivity)).trans (le_of_eq ?_))
  rw [show r * ((ε : ℝ) / 18) ^ 2 / r = ((ε : ℝ) / 18) ^ 2 by field_simp,
    Real.sqrt_sq (by positivity), show 18 * ((ε : ℝ) / 18) = ε by ring, ENNReal.ofReal_coe_nnreal]

theorem foldedCircle_ae_mem_H (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂foldedCircle w r, x ∈ H := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (foldedCircle_im_nonpos w hr)
  simp only [mem_setOf_eq] at hx ⊢
  exact not_lt.1 hx

theorem foldedCircle_ae_abs_im_le (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ x ∂foldedCircle w r, |x.im| ≤ ‖w‖ + r := by
  rw [ae_iff]
  have hB : MeasurableSet {x : ℂ | ¬ |x.im| ≤ ‖w‖ + r} :=
    (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const).measurableSet.compl
  rw [foldedCircle_apply' w r hB]
  have : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ foldH (circleMap w r θ) ∈ {x : ℂ | ¬ |x.im| ≤ ‖w‖ + r}}
      = ∅ := by
    ext θ
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    intro _
    exact (Complex.abs_im_le_norm _).trans ((norm_foldH _).le.trans
      (norm_circleMap_le_add w hr θ))
  rw [this, measure_empty, mul_zero]

/-- `log Im` is integrable against every folded circle of positive radius. -/
theorem integrable_log_im_foldedCircle (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℂ => Real.log x.im) (foldedCircle w r) := by
  set R := ‖w‖ + r
  set h : ℂ → ℝ := fun x => max (-Real.log |x.im|) 0 with hh
  have hmeas : Measurable h :=
    ((Real.measurable_log.comp (continuous_abs.measurable.comp Complex.measurable_im)).neg).max
      measurable_const
  have hint : Integrable h (foldedCircle w r) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hnn : 0 ≤ᵐ[foldedCircle w r] h := ae_of_all _ fun x => (le_max_right _ _ : (0 : ℝ) ≤ h x)
    rw [hasFiniteIntegral_iff_ofReal hnn, lintegral_eq_lintegral_meas_lt _ hnn hmeas.aemeasurable]
    have hC : Integrable (fun t : ℝ => 18 / Real.sqrt r * Real.exp (-(1 / 2) * t))
        (volume.restrict (Ioi 0)) :=
      (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
    refine lt_of_le_of_lt (setLIntegral_mono ?_ fun t (ht : 0 < t) => ?_) hC.lintegral_lt_top
    · exact ENNReal.measurable_ofReal.comp (measurable_const.mul
        (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
    · have hsub : {x : ℂ | t < h x} ⊆ {x | |x.im| < Real.exp (-t)} := by
        intro x hx
        simp only [mem_setOf_eq, hh, lt_max_iff] at hx ⊢
        rcases hx with hx | hx
        · rcases eq_or_lt_of_le (abs_nonneg x.im) with h0 | h0
          · rw [← h0, Real.log_zero] at hx; linarith
          · exact (Real.log_lt_iff_lt_exp h0).1 (by linarith)
        · linarith
      refine (measure_mono hsub).trans ((foldedCircle_strip_le w hr (Real.exp_pos _)).trans
        (le_of_eq ?_))
      congr 1
      rw [Real.sqrt_div (Real.exp_pos _).le, ← Real.exp_half,
        show -t / 2 = -(1 / 2) * t by ring]
      ring
  have hlogR : ∀ x : ℂ, |x.im| ≤ R → |Real.log x.im| ≤ h x + |Real.log R| := by
    intro x hx
    rw [← Real.log_abs x.im]
    have hmax := le_max_left (-Real.log |x.im|) 0
    have hmax0 := le_max_right (-Real.log |x.im|) 0
    rcases eq_or_lt_of_le (abs_nonneg x.im) with h0 | h0
    · rw [← h0, Real.log_zero, abs_zero]; positivity
    · have := Real.log_le_log h0 hx
      rw [abs_le]; constructor
      · simp only [hh]; linarith [abs_nonneg (Real.log R)]
      · simp only [hh]; linarith [le_abs_self (Real.log R)]
  refine (hint.add (integrable_const |Real.log R|)).mono'
    (Real.measurable_log.comp Complex.measurable_im).aestronglyMeasurable ?_
  filter_upwards [foldedCircle_ae_abs_im_le w hr.le] with x hx
  rw [Real.norm_eq_abs]
  exact hlogR x hx

/-- **(L) integrability.** `log ‖f'‖` is integrable against every folded circle. -/
theorem integrable_log_norm_deriv_revMap_foldedCircle (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun u => Real.log ‖deriv (revMap W T) u‖) (foldedCircle w r) := by
  refine ((integrable_const |Real.log (Real.sqrt ((‖w‖ + r) ^ 2 + 4 * T))|).add
    (integrable_log_im_foldedCircle w hr).abs).mono'
    (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable ?_
  filter_upwards [foldedCircle_ae_abs_im_le w hr.le, foldedCircle_ae_mem_H w hr] with x hx hxH
  rw [Real.norm_eq_abs]
  exact abs_log_norm_deriv_revMap_le hW hT hxH ((le_abs_self _).trans hx)

/-! ### (L) continuity in `(w, r)` -/

theorem re_foldH (x : ℂ) : (foldH x).re = x.re := by
  unfold foldH; split_ifs <;> simp

theorem continuous_foldH : Continuous foldH := by
  have e : foldH = fun x : ℂ => (x.re : ℂ) + ((|x.im| : ℝ) : ℂ) * I := by
    funext x; apply Complex.ext <;> simp [re_foldH, im_foldH]
  rw [e]
  exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
    ((Complex.continuous_ofReal.comp (continuous_abs.comp Complex.continuous_im)).mul
      continuous_const)

theorem foldedCircle_ae_norm_le (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ x ∂foldedCircle w r, ‖x‖ ≤ ‖w‖ + r := by
  rw [ae_iff]
  have hB : MeasurableSet {x : ℂ | ¬ ‖x‖ ≤ ‖w‖ + r} :=
    (isClosed_le continuous_norm continuous_const).measurableSet.compl
  rw [foldedCircle_apply' w r hB]
  have : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ foldH (circleMap w r θ) ∈ {x : ℂ | ¬ ‖x‖ ≤ ‖w‖ + r}}
      = ∅ := by
    ext θ
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    intro _
    exact (norm_foldH _).le.trans (norm_circleMap_le_add w hr θ)
  rw [this, measure_empty, mul_zero]

/-- Clamp the imaginary part from below at `τ`. -/
def clampIm (τ : ℝ) (u : ℂ) : ℂ := (u.re : ℂ) + ((max u.im τ : ℝ) : ℂ) * I

theorem clampIm_im (τ : ℝ) (u : ℂ) : (clampIm τ u).im = max u.im τ := by simp [clampIm]

theorem clampIm_of_le {τ : ℝ} {u : ℂ} (h : τ ≤ u.im) : clampIm τ u = u :=
  Complex.ext (by simp [clampIm]) (by simp [clampIm, max_eq_left h])

theorem continuous_clampIm (τ : ℝ) : Continuous (clampIm τ) :=
  (Complex.continuous_ofReal.comp Complex.continuous_re).add
    ((Complex.continuous_ofReal.comp (Complex.continuous_im.max continuous_const)).mul
      continuous_const)

theorem norm_clampIm_le {τ : ℝ} (hτ : 0 ≤ τ) (u : ℂ) : ‖clampIm τ u‖ ≤ 2 * ‖u‖ + τ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 : (clampIm τ u).re = u.re := by simp [clampIm]
  rw [h1, clampIm_im, abs_of_nonneg (le_max_of_le_right hτ)]
  have h2 := Complex.abs_re_le_norm u
  have h3 := Complex.abs_im_le_norm u
  have h4 : max u.im τ ≤ |u.im| + τ :=
    max_le (by linarith [le_abs_self u.im]) (by linarith [abs_nonneg u.im])
  linarith

theorem abs_log_le_of_mem {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| := by
  have h1 := Real.log_le_log ha hax
  have h2 := Real.log_le_log (ha.trans_le hax) hxb
  rw [abs_le]; constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

theorem integral_foldedCircle_eq {g : ℂ → ℝ} (hg : Measurable g) (w : ℂ) (r : ℝ) :
    ∫ u, g u ∂foldedCircle w r =
      (2 * π)⁻¹ * ∫ θ in Ico 0 (2 * π), g (foldH (circleMap w r θ)) := by
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable hg.aestronglyMeasurable,
    circleUnif, integral_smul_measure,
    integral_map (f := fun x => g (foldH x)) (measurable_circleMap w r).aemeasurable
      (hg.comp measurable_foldH).aestronglyMeasurable,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem continuous_integral_foldedCircle {g : ℂ → ℝ} (hg : Continuous g) :
    Continuous (fun p : ℂ × ℝ => ∫ u, g u ∂foldedCircle p.1 p.2) := by
  have e : (fun p : ℂ × ℝ => ∫ u, g u ∂foldedCircle p.1 p.2) = fun p =>
      (2 * π)⁻¹ * ∫ θ in Icc 0 (2 * π), g (foldH (circleMap p.1 p.2 θ)) := by
    funext p; rw [integral_foldedCircle_eq hg.measurable, integral_Icc_eq_integral_Ico]
  rw [e]
  have hc : Continuous (fun q : (ℂ × ℝ) × ℝ => circleMap q.1.1 q.1.2 q.2) := by
    simp only [circleMap]; fun_prop
  exact continuous_const.mul (continuous_parametric_integral_of_continuous
    (f := fun (p : ℂ × ℝ) (θ : ℝ) => g (foldH (circleMap p.1 p.2 θ)))
    (hg.comp (continuous_foldH.comp hc)) isCompact_Icc)

/-- Layer-cake bound for `log⁺ (τ / Im)` against a folded circle. -/
theorem lintegral_logRatio_le (w : ℂ) {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ) :
    ∫⁻ u, ENNReal.ofReal (max (Real.log (τ / |u.im|)) 0) ∂foldedCircle w r ≤
      ENNReal.ofReal (36 * Real.sqrt (τ / r)) := by
  set h : ℂ → ℝ := fun u => max (Real.log (τ / |u.im|)) 0 with hh
  have hmeas : Measurable h :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp Complex.measurable_im))).max measurable_const
  have hnn : 0 ≤ᵐ[foldedCircle w r] h := ae_of_all _ fun x => (le_max_right _ _ : (0 : ℝ) ≤ h x)
  rw [lintegral_eq_lintegral_meas_lt _ hnn hmeas.aemeasurable]
  have hC : Integrable (fun t : ℝ => 18 * Real.sqrt (τ / r) * Real.exp (-(1 / 2) * t))
      (volume.restrict (Ioi 0)) :=
    (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  have hval : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (18 * Real.sqrt (τ / r) *
      Real.exp (-(1 / 2) * t)) = ENNReal.ofReal (36 * Real.sqrt (τ / r)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hC (ae_of_all _ fun t => by positivity),
      integral_const_mul, integral_exp_mul_Ioi (by norm_num) 0,
      show (-(1 / 2 : ℝ)) * 0 = 0 by ring, Real.exp_zero]
    congr 1; ring
  rw [← hval]
  refine setLIntegral_mono (ENNReal.measurable_ofReal.comp (measurable_const.mul
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)))) fun t (ht : 0 < t) => ?_
  have hsub : {x : ℂ | t < h x} ⊆ {x | |x.im| < τ * Real.exp (-t)} := by
    intro x hx
    simp only [mem_setOf_eq, hh, lt_max_iff] at hx ⊢
    rcases hx with hx | hx
    · rcases eq_or_lt_of_le (abs_nonneg x.im) with h0 | h0
      · rw [← h0, div_zero, Real.log_zero] at hx; linarith
      · have h1 := (Real.lt_log_iff_exp_lt (div_pos hτ h0)).1 hx
        rw [lt_div_iff₀ h0] at h1
        rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos t)]
        linarith [mul_comm |x.im| (Real.exp t)]
    · linarith
  refine (measure_mono hsub).trans ((foldedCircle_strip_le w hr (by positivity)).trans
    (le_of_eq ?_))
  congr 1
  rw [show τ * Real.exp (-t) / r = τ / r * Real.exp (-t) by ring,
    Real.sqrt_mul (by positivity), ← Real.exp_half, show -t / 2 = -(1 / 2) * t by ring]
  ring

theorem integrable_of_log_bound {G : ℂ → ℝ} (hGm : Measurable G) {A R : ℝ}
    (hGb : ∀ u ∈ H, ‖u‖ ≤ R → |G u| ≤ A + |Real.log u.im|) (w : ℂ) {r : ℝ} (hr : 0 < r)
    (hwR : ‖w‖ + r ≤ R) : Integrable G (foldedCircle w r) := by
  refine ((integrable_const A).add (integrable_log_im_foldedCircle w hr).abs).mono'
    hGm.aestronglyMeasurable ?_
  filter_upwards [foldedCircle_ae_norm_le w hr.le, foldedCircle_ae_mem_H w hr] with x hx hxH
  rw [Real.norm_eq_abs]
  exact hGb x hxH (hx.trans hwR)

/-- The truncation error `∫ |G − G ∘ clampIm τ| dσ` is `O(√τ · (1 + |log τ|))`, uniformly. -/
theorem integral_abs_sub_clamp_le {G : ℂ → ℝ} (hGm : Measurable G) {A R : ℝ} (hA : 0 ≤ A)
    (hGb : ∀ u ∈ H, ‖u‖ ≤ 2 * R + 1 → |G u| ≤ A + |Real.log u.im|) (w : ℂ) {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hwR : ‖w‖ + r ≤ R) :
    ∫ u, |G u - G (clampIm τ u)| ∂foldedCircle w r ≤
      18 * Real.sqrt (τ / r) * (2 * A + 2 * |Real.log τ| + 4) := by
  set σ := foldedCircle w r
  set c := 2 * A + 2 * |Real.log τ|
  set h : ℂ → ℝ := fun u => max (Real.log (τ / |u.im|)) 0 with hh
  have hmeas : Measurable h :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp Complex.measurable_im))).max measurable_const
  have hnn : 0 ≤ᵐ[σ] h := ae_of_all _ fun x => (le_max_right _ _ : (0 : ℝ) ≤ h x)
  have hlin := lintegral_logRatio_le w hr hτ
  have hhint : Integrable h σ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hhle : ∫ u, h u ∂σ ≤ 36 * Real.sqrt (τ / r) := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  have hS : MeasurableSet {u : ℂ | |u.im| < τ} :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).measurableSet
  have hc0 : 0 ≤ c := by positivity
  have hc : c = 2 * A + 2 * |Real.log τ| := rfl
  have hR : 0 ≤ R := by linarith [norm_nonneg w]
  have hSle : σ.real {u : ℂ | |u.im| < τ} ≤ 18 * Real.sqrt (τ / r) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (foldedCircle_strip_le w hr hτ)
  have hpt : ∀ᵐ u ∂σ, |G u - G (clampIm τ u)| ≤
      {u : ℂ | |u.im| < τ}.indicator (fun _ => c) u + 2 * h u := by
    filter_upwards [foldedCircle_ae_norm_le w hr.le, foldedCircle_ae_mem_H w hr] with u hu huH
    have huH' : 0 < u.im := huH
    have hh0 : 0 ≤ h u := le_max_right _ _
    rcases le_or_gt τ u.im with h1 | h1
    · rw [clampIm_of_le h1, sub_self, abs_zero]
      have : 0 ≤ {u : ℂ | |u.im| < τ}.indicator (fun _ => c) u :=
        Set.indicator_nonneg (fun _ _ => hc0) u
      linarith
    · have hmem : u ∈ {u : ℂ | |u.im| < τ} := by
        simp only [mem_setOf_eq]; rw [abs_of_pos huH']; exact h1
      rw [Set.indicator_of_mem hmem]
      have hG1 := hGb u huH (by linarith [norm_nonneg u])
      have hcl : clampIm τ u ∈ H :=
        show 0 < (clampIm τ u).im by rw [clampIm_im]; exact lt_max_of_lt_right hτ
      have hG2 := hGb _ hcl ((norm_clampIm_le hτ.le u).trans (by linarith))
      rw [clampIm_im, max_eq_right h1.le] at hG2
      have hlogu : |Real.log u.im| ≤ h u + |Real.log τ| := by
        have hneg : Real.log u.im < 0 := Real.log_neg huH' (by linarith)
        rw [abs_of_neg hneg]
        have e : Real.log (τ / |u.im|) = Real.log τ - Real.log u.im := by
          rw [abs_of_pos huH', Real.log_div hτ.ne' huH'.ne']
        have : Real.log (τ / |u.im|) ≤ h u := le_max_left _ _
        linarith [neg_abs_le (Real.log τ)]
      rw [abs_sub_le_iff]
      constructor
      · linarith [le_abs_self (G u), neg_abs_le (G (clampIm τ u))]
      · linarith [neg_abs_le (G u), le_abs_self (G (clampIm τ u))]
  have hi1 : Integrable ({u : ℂ | |u.im| < τ}.indicator (fun _ => c)) σ :=
    (integrable_const c).indicator hS
  refine (integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _)
    (hi1.add (hhint.const_mul 2)) hpt).trans ?_
  show ∫ a, ({u : ℂ | |u.im| < τ}.indicator (fun _ => c) a + 2 * h a) ∂σ ≤ _
  rw [integral_add hi1 (hhint.const_mul 2), integral_indicator_const c hS, integral_const_mul,
    smul_eq_mul]
  have := mul_le_mul_of_nonneg_right hSle hc0
  nlinarith [this, hhle]

theorem exists_tail_small {K c ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ τ, 0 < τ ∧ τ ≤ 1 ∧ K * Real.sqrt τ * (c + 2 * |Real.log τ|) < ε := by
  have h1 : Tendsto (fun τ : ℝ => Real.log τ * τ ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
  have h2 : Tendsto (fun τ : ℝ => τ ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Real.sqrt_eq_rpow] using this
  have h3 : Tendsto (fun τ : ℝ => K * (c * τ ^ (1 / 2 : ℝ) - 2 * (Real.log τ * τ ^ (1 / 2 : ℝ))))
      (𝓝[>] 0) (𝓝 (K * (c * 0 - 2 * 0))) :=
    ((h2.const_mul c).sub (h1.const_mul 2)).const_mul K
  rw [show K * (c * 0 - 2 * 0) = 0 by ring] at h3
  have ev1 := h3.eventually (gt_mem_nhds hε)
  have ev2 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Ioo 0 1 := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨τ, hτε, hτ⟩ := (ev1.and ev2).exists
  refine ⟨τ, hτ.1, hτ.2.le, ?_⟩
  have hlog : |Real.log τ| = -Real.log τ := abs_of_neg (Real.log_neg hτ.1 hτ.2)
  rw [hlog, Real.sqrt_eq_rpow]
  calc K * τ ^ (1 / 2 : ℝ) * (c + 2 * -Real.log τ)
      = K * (c * τ ^ (1 / 2 : ℝ) - 2 * (Real.log τ * τ ^ (1 / 2 : ℝ))) := by ring
    _ < ε := hτε

/-- **Continuity in `(w, r)`** of `∫ G dfc(w,r)` for `G` continuous on `H` with a
`A + |log Im|` bound on bounded sets. -/
theorem continuousOn_integral_foldedCircle {G : ℂ → ℝ} (hGm : Measurable G)
    (hGc : ContinuousOn G H)
    (hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ u ∈ H, ‖u‖ ≤ R → |G u| ≤ A + |Real.log u.im|) :
    ContinuousOn (fun p : ℂ × ℝ => ∫ u, G u ∂foldedCircle p.1 p.2) {p | 0 < p.2} := by
  intro p₀ hp₀
  have hr₀ : 0 < p₀.2 := hp₀
  refine ContinuousAt.continuousWithinAt ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  set R := ‖p₀.1‖ + p₀.2 + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨A, hA0, hA⟩ := hGb (2 * R + 1)
  obtain ⟨τ, hτ0, hτ1, hτε⟩ := exists_tail_small (K := 18 * Real.sqrt (2 / p₀.2))
    (c := 2 * A + 4) (by positivity) (by positivity : 0 < ε / 3)
  set Gτ : ℂ → ℝ := fun u => G (clampIm τ u) with hGτ
  have hGτc : Continuous Gτ := hGc.comp_continuous (continuous_clampIm τ) fun u =>
    show 0 < (clampIm τ u).im by rw [clampIm_im]; exact lt_max_of_lt_right hτ0
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1
    (continuous_integral_foldedCircle hGτc).continuousAt (ε / 3) (by positivity)
  have tail : ∀ q : ℂ × ℝ, p₀.2 / 2 ≤ q.2 → ‖q.1‖ + q.2 ≤ R →
      |(∫ u, G u ∂foldedCircle q.1 q.2) - ∫ u, Gτ u ∂foldedCircle q.1 q.2| < ε / 3 := by
    intro q hq1 hq2
    have hq0 : 0 < q.2 := by linarith
    have hint1 := integrable_of_log_bound hGm hA q.1 hq0 (by linarith)
    have hint2 : Integrable Gτ (foldedCircle q.1 q.2) := by
      refine (integrable_const (A + |Real.log τ| + |Real.log (2 * R + 1)|)).mono'
        hGτc.measurable.aestronglyMeasurable ?_
      filter_upwards [foldedCircle_ae_norm_le q.1 hq0.le] with u hu
      have hcl : clampIm τ u ∈ H :=
        show 0 < (clampIm τ u).im by rw [clampIm_im]; exact lt_max_of_lt_right hτ0
      have hG2 := hA _ hcl ((norm_clampIm_le hτ0.le u).trans (by linarith))
      rw [clampIm_im] at hG2
      have hmax : max u.im τ ≤ 2 * R + 1 :=
        max_le (by linarith [Complex.im_le_norm u]) (by linarith)
      have hl := abs_log_le_of_mem hτ0 (le_max_right u.im τ) hmax
      rw [Real.norm_eq_abs]
      linarith
    rw [← integral_sub hint1 hint2]
    refine abs_integral_le_integral_abs.trans_lt ?_
    refine (integral_abs_sub_clamp_le hGm hA0 (R := R) hA q.1 hq0 hτ0 hτ1 hq2).trans_lt ?_
    refine lt_of_le_of_lt ?_ hτε
    have hs : Real.sqrt (τ / q.2) ≤ Real.sqrt (2 / p₀.2) * Real.sqrt τ := by
      rw [← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      calc τ / q.2 ≤ τ / (p₀.2 / 2) := div_le_div_of_nonneg_left hτ0.le (by positivity) hq1
        _ = 2 / p₀.2 * τ := by field_simp
    have hf : 0 ≤ 2 * A + 2 * |Real.log τ| + 4 := by positivity
    calc 18 * Real.sqrt (τ / q.2) * (2 * A + 2 * |Real.log τ| + 4)
        ≤ 18 * (Real.sqrt (2 / p₀.2) * Real.sqrt τ) * (2 * A + 2 * |Real.log τ| + 4) := by
          gcongr
      _ = 18 * Real.sqrt (2 / p₀.2) * Real.sqrt τ * (2 * A + 4 + 2 * |Real.log τ|) := by ring
  refine ⟨min δ₁ (min 1 (p₀.2 / 2)), by positivity, fun p hp => ?_⟩
  have hp1 : dist p p₀ < δ₁ := hp.trans_le (min_le_left _ _)
  have hp2 : dist p p₀ < 1 := hp.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hp3 : dist p p₀ < p₀.2 / 2 := hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  rw [Prod.dist_eq, max_lt_iff] at hp2 hp3
  rw [dist_eq_norm] at hp2
  rw [Real.dist_eq, abs_lt] at hp2 hp3
  have hn : ‖p.1‖ ≤ ‖p₀.1‖ + ‖p.1 - p₀.1‖ := by
    have := norm_sub_norm_le p.1 p₀.1; linarith
  have t1 := abs_lt.1 (tail p (by linarith [hp3.2.1]) (by linarith [hp2.1, hp2.2.2]))
  have t3 := abs_lt.1 (tail p₀ (by linarith) (by linarith))
  have t2 : |(∫ u, Gτ u ∂foldedCircle p.1 p.2) - ∫ u, Gτ u ∂foldedCircle p₀.1 p₀.2| < ε / 3 := by
    have := hδ₁' hp1; rwa [Real.dist_eq] at this
  have t2' := abs_lt.1 t2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [t1.1, t1.2, t2'.1, t2'.2, t3.1, t3.2]

end Circles

end TwoPoint
end QuantumZipper
