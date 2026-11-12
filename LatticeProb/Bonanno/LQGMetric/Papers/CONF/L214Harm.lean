/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L214Harm at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.LWExc2Poisson
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14, node R1: a harmonic minorant of the harmonic measure of `J⁻` in `H_I`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), proof of Lemma 2.14,
confluence-final.tex 863: "The probability that a Brownian motion started from `w_I` exits `H_I`
at a point in `J_I⁻` is at least some universal constant `a > 0`." We prove the analytic form
needed for the Beurling step, in normalized coordinates where the centre of the arc is `u_I = i`,
so `H_I` is the upper half-disc `upperHalfDisc` and `w_I = (1 − ℓ) i`; `J_I⁻` has angles
`[π/2 − 3ℓ/2, π/2 − ℓ/2]` and centre `c⁻ = e^{i(π/2 − ℓ)}` (`l214CenterM ℓ`).

`l214_minorant`: for `0 < ℓ ≤ 1/10` the function `g = P[f − f ∘ conj]` (Poisson integral of a
tent `f` of height 1 on the cap `|ζ − c⁻| < ℓ/4`, which lies in `J_I⁻`, minus its mirror image)
is harmonic on `𝔻`, has values in `[0, 1]` on the upper half-disc, satisfies
`g(w_I) ≥ 1/(128π)`, and tends to `0` at every boundary point of the upper half-disc at distance
`≥ ℓ/4` from `c⁻`. It is a minorant of the harmonic measure of `J_I⁻` in `H_I`, which is all the
argument at C:863–869 uses (the Beurling step only needs a harmonic `h ∈ [0,1]` vanishing on the
rest of the boundary with `h(w_I) ≥ a`).

Sources: Poisson integral, its harmonicity, boundary values and vanishing on the diameter for
conjugation-odd data are QuantumZipper's `lwPoisson`, `lwExc2_poisson_harm`,
`lwExc2_poisson_tendsto`, `lwExc2_poisson_odd` (Ahlfors, *Complex Analysis*, Ch. 4 §6, Thms 23–24
— the reflection construction of harmonic measure in a half-disc). The explicit lower bound at
`w_I` (Poisson kernel estimates) is an own elementary computation. The smaller range
`ℓ ≤ 1/10` (CONF: `r_I ≤ π/4`) only changes the universal constant of the long-arc count
(`confL214_long_arcs`-type bound); see DEVIATIONS (proposed DV-CONF-214d).
-/

namespace LQGMetric
namespace CONF

open Set Metric Filter Complex
open scoped Topology Real ComplexConjugate

open QuantumZipper.Thm18Asm.LWFar (lwPoisson)

/-- The open upper half-disc (CONF's `H_I` in coordinates with `u_I = i`). -/
def upperHalfDisc : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.im}

theorem upperHalfDisc_subset_ball : upperHalfDisc ⊆ ball (0 : ℂ) 1 := fun z hz =>
  mem_ball_zero_iff.2 hz.1

/-- Centre `c⁻ = e^{i(π/2 − ℓ)}` of the arc `J⁻` (normalized coordinates). -/
noncomputable def l214CenterM (ℓ : ℝ) : ℂ := exp (((π / 2 - ℓ : ℝ) : ℂ) * I)

/-- Tent of height `1` on the cap `|ζ − c⁻| < ℓ/4`. -/
noncomputable def l214Bump (ℓ : ℝ) (ζ : ℂ) : ℝ := max 0 (1 - 4 * ‖ζ - l214CenterM ℓ‖ / ℓ)

/-- Conjugation-odd boundary data `f − f ∘ conj`. -/
noncomputable def l214Data (ℓ : ℝ) (ζ : ℂ) : ℝ := l214Bump ℓ ζ - l214Bump ℓ (conj ζ)

/-- The harmonic minorant `g = P[f − f ∘ conj]`. -/
noncomputable def l214Harm (ℓ : ℝ) : ℂ → ℝ := lwPoisson (l214Data ℓ) 1

theorem l214CenterM_re (ℓ : ℝ) : (l214CenterM ℓ).re = Real.sin ℓ := by
  rw [l214CenterM, exp_ofReal_mul_I_re, Real.cos_pi_div_two_sub]

theorem l214CenterM_im (ℓ : ℝ) : (l214CenterM ℓ).im = Real.cos ℓ := by
  rw [l214CenterM, exp_ofReal_mul_I_im, Real.sin_pi_div_two_sub]

theorem continuous_l214Bump (ℓ : ℝ) : Continuous (l214Bump ℓ) := by
  unfold l214Bump; fun_prop

theorem continuous_l214Data (ℓ : ℝ) : Continuous (l214Data ℓ) := by
  unfold l214Data
  exact (continuous_l214Bump ℓ).sub ((continuous_l214Bump ℓ).comp continuous_conj)

theorem l214Bump_nonneg (ℓ : ℝ) (ζ : ℂ) : 0 ≤ l214Bump ℓ ζ := le_max_left _ _

theorem l214Bump_le_one {ℓ : ℝ} (hℓ : 0 < ℓ) (ζ : ℂ) : l214Bump ℓ ζ ≤ 1 := by
  unfold l214Bump
  refine max_le zero_le_one ?_
  have : 0 ≤ 4 * ‖ζ - l214CenterM ℓ‖ / ℓ := by positivity
  linarith

theorem l214Bump_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {ζ : ℂ} (h : ℓ / 4 ≤ ‖ζ - l214CenterM ℓ‖) :
    l214Bump ℓ ζ = 0 := by
  unfold l214Bump
  refine max_eq_left ?_
  have : 1 ≤ 4 * ‖ζ - l214CenterM ℓ‖ / ℓ := by rw [le_div_iff₀ hℓ]; linarith
  linarith

theorem l214Bump_ge_half {ℓ : ℝ} (hℓ : 0 < ℓ) {ζ : ℂ} (h : ‖ζ - l214CenterM ℓ‖ ≤ ℓ / 8) :
    1 / 2 ≤ l214Bump ℓ ζ := by
  unfold l214Bump
  refine le_max_of_le_right ?_
  have : 4 * ‖ζ - l214CenterM ℓ‖ / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; linarith
  linarith

/-- `cos ℓ ≥ 1 − ℓ²/2 ≥ 9/10` for `0 < ℓ ≤ 1/10`. -/
theorem l214_cos_ge {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) : 9 / 10 ≤ Real.cos ℓ := by
  have := Real.one_sub_sq_div_two_le_cos (x := ℓ); nlinarith

/-- Points near `c⁻` lie in the upper half-plane. -/
theorem l214_im_pos_of_near {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) {ζ : ℂ}
    (h : ‖ζ - l214CenterM ℓ‖ < ℓ / 4) : 1 / 2 < ζ.im := by
  have h1 := (abs_im_le_norm (ζ - l214CenterM ℓ)).trans_lt h
  rw [sub_im, l214CenterM_im] at h1
  have := l214_cos_ge hℓ hℓ1
  have := (abs_lt.1 h1).1
  linarith

theorem l214Bump_pos_im {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) {ζ : ℂ}
    (h : 0 < l214Bump ℓ ζ) : 0 < ζ.im := by
  by_contra hc
  have : ℓ / 4 ≤ ‖ζ - l214CenterM ℓ‖ := by
    by_contra h'; push_neg at h'
    have := l214_im_pos_of_near hℓ hℓ1 h'; linarith
  rw [l214Bump_eq_zero hℓ this] at h; exact lt_irrefl _ h

theorem l214Bump_conj_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) {ζ : ℂ}
    (h : 0 ≤ ζ.im) : l214Bump ℓ (conj ζ) = 0 := by
  rcases (l214Bump_nonneg ℓ (conj ζ)).lt_or_eq with h' | h'
  · have := l214Bump_pos_im hℓ hℓ1 h'; rw [conj_im] at this; linarith
  · exact h'.symm

theorem l214Data_conj (ℓ : ℝ) (ζ : ℂ) : l214Data ℓ (conj ζ) = - l214Data ℓ ζ := by
  simp [l214Data]

theorem harmonicOnNhd_l214Harm (ℓ : ℝ) :
    InnerProductSpace.HarmonicOnNhd (l214Harm ℓ) (ball (0 : ℂ) 1) := by
  have := QuantumZipper.Thm18Asm.LWFar.lwExc2_poisson_harm one_pos
    (continuous_l214Data ℓ).continuousOn 0
  simpa [l214Harm] using this

/-- `P(z, ζ) ≥ P(z, ζ̄)` for `z, ζ` in the closed upper half-plane, `|z| < 1 = |ζ|`. -/
theorem poissonKernel_conj_le {z ζ : ℂ} (hz : ‖z‖ < 1) (hzi : 0 ≤ z.im) (hζ : ‖ζ‖ = 1)
    (hζi : 0 ≤ ζ.im) : poissonKernel 0 z (conj ζ) ≤ poissonKernel 0 z ζ := by
  simp only [poissonKernel_def, sub_zero, Complex.norm_conj, hζ]
  have hnum : 0 ≤ (1 : ℝ) ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hne : ζ - z ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hζ; linarith
  have hpos : 0 < ‖ζ - z‖ ^ 2 := by positivity
  apply div_le_div_of_nonneg_left hnum hpos
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, sub_im, conj_re, conj_im]
  nlinarith

/-- The pairing formula `g(z) = ⨍ (P(z, ζ) − P(z, ζ̄)) f(ζ)`. -/
theorem l214Harm_eq (ℓ : ℝ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    l214Harm ℓ z = Real.circleAverage
      (fun ζ => (poissonKernel 0 z ζ - poissonKernel 0 z (conj ζ)) * l214Bump ℓ ζ) 0 1 := by
  have hs : sphere (0 : ℂ) |(1 : ℝ)| = sphere 0 1 := by simp
  have hP := QuantumZipper.Thm18Asm.LWFar.lwExc2_pk_cont hz
  have hPc : ContinuousOn (fun ζ => poissonKernel 0 z (conj ζ)) (sphere (0 : ℂ) 1) :=
    hP.comp continuous_conj.continuousOn fun ζ hζ => by simpa using hζ
  have hB := (continuous_l214Bump ℓ).continuousOn (s := sphere (0 : ℂ) 1)
  have hBc := ((continuous_l214Bump ℓ).comp continuous_conj).continuousOn
    (s := sphere (0 : ℂ) 1)
  have i1 : CircleIntegrable (fun ζ => poissonKernel 0 z ζ * l214Bump ℓ ζ) 0 1 :=
    ContinuousOn.circleIntegrable' (by rw [hs]; exact hP.mul hB)
  have i2 : CircleIntegrable (fun ζ => poissonKernel 0 z ζ * l214Bump ℓ (conj ζ)) 0 1 :=
    ContinuousOn.circleIntegrable' (by rw [hs]; exact hP.mul hBc)
  have i3 : CircleIntegrable (fun ζ => poissonKernel 0 z (conj ζ) * l214Bump ℓ ζ) 0 1 :=
    ContinuousOn.circleIntegrable' (by rw [hs]; exact hPc.mul hB)
  have hconj := QuantumZipper.Thm18Asm.LWFar.lwExc2_circleAverage_conj
    (fun ζ => poissonKernel 0 z (conj ζ) * l214Bump ℓ ζ) 1
  simp only [Complex.conj_conj] at hconj
  calc l214Harm ℓ z
      = Real.circleAverage (fun ζ => poissonKernel 0 z ζ * l214Bump ℓ ζ -
          poissonKernel 0 z ζ * l214Bump ℓ (conj ζ)) 0 1 := by
        unfold l214Harm lwPoisson l214Data; congr 1; funext ζ; ring
    _ = Real.circleAverage (fun ζ => poissonKernel 0 z ζ * l214Bump ℓ ζ) 0 1 -
          Real.circleAverage (fun ζ => poissonKernel 0 z (conj ζ) * l214Bump ℓ ζ) 0 1 := by
        rw [Real.circleAverage_fun_sub i1 i2, hconj]
    _ = _ := by
        rw [← Real.circleAverage_fun_sub i1 i3]; congr 1; funext ζ; ring

theorem l214_sphere_abs : sphere (0 : ℂ) |(1 : ℝ)| = sphere 0 1 := by simp

/-- The integrand of the pairing formula is nonnegative on the circle when `z` is in the upper
half-disc (closure). -/
theorem l214_integrand_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) {z ζ : ℂ} (hz : ‖z‖ < 1)
    (hzi : 0 ≤ z.im) (hζ : ‖ζ‖ = 1) :
    0 ≤ (poissonKernel 0 z ζ - poissonKernel 0 z (conj ζ)) * l214Bump ℓ ζ := by
  rcases (l214Bump_nonneg ℓ ζ).lt_or_eq with h | h
  · have hi := l214Bump_pos_im hℓ hℓ1 h
    exact mul_nonneg (sub_nonneg.2 (poissonKernel_conj_le hz hzi hζ hi.le)) h.le
  · rw [← h, mul_zero]

/-- `0 ≤ g ≤ 1` on the upper half-disc. -/
theorem l214Harm_mem_Icc {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) {z : ℂ}
    (hz : z ∈ upperHalfDisc) : 0 ≤ l214Harm ℓ z ∧ l214Harm ℓ z ≤ 1 := by
  have hzb := upperHalfDisc_subset_ball hz
  constructor
  · rw [l214Harm_eq ℓ hzb]
    refine Real.circleAverage_nonneg_of_nonneg fun ζ hζ => ?_
    rw [l214_sphere_abs, mem_sphere_zero_iff_norm] at hζ
    exact l214_integrand_nonneg hℓ hℓ1 hz.1 hz.2.le hζ
  · have hP := QuantumZipper.Thm18Asm.LWFar.lwExc2_pk_cont hzb
    have i1 : CircleIntegrable (fun ζ => poissonKernel 0 z ζ * l214Data ℓ ζ) 0 1 :=
      ContinuousOn.circleIntegrable'
        (by rw [l214_sphere_abs]; exact hP.mul (continuous_l214Data ℓ).continuousOn)
    have i2 : CircleIntegrable (poissonKernel 0 z) 0 1 :=
      ContinuousOn.circleIntegrable' (by rw [l214_sphere_abs]; exact hP)
    rw [← QuantumZipper.Thm18Asm.LWFar.lwExc2_pk_avg one_pos hzb]
    refine Real.circleAverage_mono i1 i2 fun ζ hζ => ?_
    rw [l214_sphere_abs] at hζ
    have hP0 := QuantumZipper.Thm18Asm.LWFar.lwExc2_pk_nonneg hzb hζ
    have : l214Data ℓ ζ ≤ 1 := by
      unfold l214Data
      linarith [l214Bump_le_one hℓ ζ, l214Bump_nonneg ℓ (conj ζ)]
    nlinarith

/-- Pointwise lower bound of the integrand near `c⁻`: `≥ 1/(16ℓ)` at `w = (1 − ℓ) i`. -/
theorem l214_integrand_ge {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hnear : ‖ζ - l214CenterM ℓ‖ ≤ ℓ / 8) :
    1 / (16 * ℓ) ≤ (poissonKernel 0 (((1 - ℓ : ℝ) : ℂ) * I) ζ -
      poissonKernel 0 (((1 - ℓ : ℝ) : ℂ) * I) (conj ζ)) * l214Bump ℓ ζ := by
  set w : ℂ := ((1 - ℓ : ℝ) : ℂ) * I with hw
  have hwre : w.re = 0 := by simp [hw]
  have hwim : w.im = 1 - ℓ := by simp [hw]
  have hwn : ‖w‖ = 1 - ℓ := by
    rw [hw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hc := l214_cos_ge hℓ hℓ1
  have hcos1 := Real.cos_le_one ℓ
  have hcos2 := Real.one_sub_sq_div_two_le_cos (x := ℓ)
  have hsin1 := Real.sin_le hℓ.le
  have hsin0 : 0 ≤ Real.sin ℓ := Real.sin_nonneg_of_nonneg_of_le_pi hℓ.le (by
    linarith [Real.pi_gt_three])
  -- `|c⁻ − w| ≤ 3ℓ/2`
  have hcw : ‖l214CenterM ℓ - w‖ ≤ 3 * ℓ / 2 := by
    have hsq : ‖l214CenterM ℓ - w‖ ^ 2 ≤ (3 * ℓ / 2) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [sub_re, sub_im, l214CenterM_re, l214CenterM_im, hwre, hwim]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have hzw : ‖ζ - w‖ ≤ 2 * ℓ := by
    have := norm_sub_le_norm_sub_add_norm_sub ζ (l214CenterM ℓ) w
    linarith
  have hne : ζ - w ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, hwn] at hζ; linarith
  have hpos : 0 < ‖ζ - w‖ ^ 2 := by positivity
  have hP1 : 1 / (4 * ℓ) ≤ poissonKernel 0 w ζ := by
    rw [poissonKernel_def]; simp only [sub_zero, hζ, hwn]
    rw [div_le_div_iff₀ (by positivity) hpos]
    have : ‖ζ - w‖ ^ 2 ≤ (2 * ℓ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzw 2
    nlinarith
  have hζim : 0 ≤ ζ.im := by
    have := l214_im_pos_of_near hℓ hℓ1 (ζ := ζ) (by linarith); linarith
  have hP2 : poissonKernel 0 w (conj ζ) ≤ 3 * ℓ := by
    rw [poissonKernel_def]; simp only [sub_zero, Complex.norm_conj, hζ, hwn]
    have hlow : 1 - ℓ ≤ ‖conj ζ - w‖ := by
      have := abs_im_le_norm (conj ζ - w)
      rw [sub_im, conj_im, hwim, abs_of_nonpos (by linarith)] at this
      linarith
    have hlow2 : (9 / 10) ^ 2 ≤ ‖conj ζ - w‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hB := l214Bump_ge_half hℓ hnear
  have hdiff : 1 / (8 * ℓ) ≤ poissonKernel 0 w ζ - poissonKernel 0 w (conj ζ) := by
    have h1 : 1 / (4 * ℓ) - 1 / (8 * ℓ) = 1 / (8 * ℓ) := by field_simp; ring
    have h2 : 3 * ℓ ≤ 1 / (8 * ℓ) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  calc 1 / (16 * ℓ) = 1 / (8 * ℓ) * (1 / 2) := by field_simp; ring
    _ ≤ _ := mul_le_mul hdiff hB (by norm_num) (by
        have : (0 : ℝ) < 1 / (8 * ℓ) := by positivity
        linarith)

/-- **Lower bound at `w_I`** (CONF C:863): `g((1 − ℓ) i) ≥ 1/(128π)`. -/
theorem l214Harm_ge {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) :
    1 / (128 * π) ≤ l214Harm ℓ (((1 - ℓ : ℝ) : ℂ) * I) := by
  set w : ℂ := ((1 - ℓ : ℝ) : ℂ) * I with hw
  have hwn : ‖w‖ = 1 - ℓ := by
    rw [hw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hwb : w ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff, hwn]; linarith
  set D : ℂ → ℝ := fun ζ => (poissonKernel 0 w ζ - poissonKernel 0 w (conj ζ)) *
    l214Bump ℓ ζ with hD
  have hP := QuantumZipper.Thm18Asm.LWFar.lwExc2_pk_cont hwb
  have hPc : ContinuousOn (fun ζ => poissonKernel 0 w (conj ζ)) (sphere (0 : ℂ) 1) :=
    hP.comp continuous_conj.continuousOn fun ζ hζ => by simpa using hζ
  have hDc : ContinuousOn D (sphere (0 : ℂ) 1) :=
    (hP.sub hPc).mul (continuous_l214Bump ℓ).continuousOn
  have hDi : CircleIntegrable D 0 1 :=
    ContinuousOn.circleIntegrable' (by rw [l214_sphere_abs]; exact hDc)
  have hcm : ∀ θ : ℝ, ‖circleMap 0 1 θ‖ = 1 := fun θ => by simp
  have hDnn : ∀ θ : ℝ, 0 ≤ D (circleMap 0 1 θ) := fun θ =>
    l214_integrand_nonneg hℓ hℓ1 (by rw [hwn]; linarith) (by simp [hw]; linarith) (hcm θ)
  set θc : ℝ := π / 2 - ℓ with hθc
  have hpi := Real.pi_gt_three
  have hint : ℓ / 4 * (1 / (16 * ℓ)) ≤ ∫ θ in (θc - ℓ / 8)..(θc + ℓ / 8), D (circleMap 0 1 θ) := by
    have hle : θc - ℓ / 8 ≤ θc + ℓ / 8 := by linarith
    have hsub : IntervalIntegrable (fun θ => D (circleMap 0 1 θ)) MeasureTheory.volume
        (θc - ℓ / 8) (θc + ℓ / 8) :=
      hDi.mono_set (by
        rw [uIcc_of_le hle, uIcc_of_le (by positivity)]
        exact Icc_subset_Icc (by linarith) (by linarith))
    have := intervalIntegral.integral_mono_on hle intervalIntegrable_const hsub
      (f := fun _ => 1 / (16 * ℓ)) fun θ hθ => by
        apply l214_integrand_ge hℓ hℓ1 (hcm θ)
        have e : circleMap 0 1 θ - l214CenterM ℓ =
            l214CenterM ℓ * (exp (I * ((θ - θc : ℝ) : ℂ)) - 1) := by
          simp only [circleMap, zero_add, l214CenterM, hθc]
          rw [mul_sub, mul_one, ← Complex.exp_add]
          congr 2; push_cast; ring
        rw [e, norm_mul, l214CenterM, norm_exp_ofReal_mul_I, one_mul]
        refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hθ.1, hθ.2]
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    convert this using 1; ring
  have hmono : ∫ θ in (θc - ℓ / 8)..(θc + ℓ / 8), D (circleMap 0 1 θ) ≤
      ∫ θ in (0 : ℝ)..2 * π, D (circleMap 0 1 θ) :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun θ => hDnn θ) hDi
  rw [l214Harm_eq ℓ hwb, Real.circleAverage_def, smul_eq_mul]
  have h64 : ℓ / 4 * (1 / (16 * ℓ)) = 1 / 64 := by field_simp; ring
  rw [h64] at hint
  have : 1 / (128 * π) = (2 * π)⁻¹ * (1 / 64) := by field_simp; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (hint.trans hmono) (by positivity)

/-- **Boundary behaviour**: `g → 0` at every point `ζ` of the boundary of the upper half-disc
(`|ζ| = 1` or `Im ζ = 0`, with `Im ζ ≥ 0`, `|ζ| ≤ 1`) at distance `≥ ℓ/4` from `c⁻`. -/
theorem l214Harm_tendsto_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) {ζ : ℂ} (hζ1 : ‖ζ‖ ≤ 1)
    (hζi : 0 ≤ ζ.im) (hbd : ‖ζ‖ = 1 ∨ ζ.im = 0) (hfar : ℓ / 4 ≤ ‖ζ - l214CenterM ℓ‖) :
    Tendsto (l214Harm ℓ) (𝓝[upperHalfDisc] ζ) (𝓝 0) := by
  rcases hζ1.lt_or_eq with hlt | heq
  · have hb : ζ ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 hlt
    have him : ζ.im = 0 := hbd.resolve_left hlt.ne
    have hc : ContinuousAt (l214Harm ℓ) ζ := (harmonicOnNhd_l214Harm ℓ ζ hb).1.continuousAt
    have h0 : l214Harm ℓ ζ = 0 :=
      QuantumZipper.Thm18Asm.LWFar.lwExc2_poisson_odd one_pos
        (fun ζ _ => l214Data_conj ℓ ζ) him
    rw [← h0]; exact tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto
  · have hs : ζ ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 heq
    have h := QuantumZipper.Thm18Asm.LWFar.lwExc2_poisson_tendsto one_pos
      (continuous_l214Data ℓ).continuousOn hs
    have h0 : l214Data ℓ ζ = 0 := by
      rw [l214Data, l214Bump_eq_zero hℓ hfar, l214Bump_conj_eq_zero hℓ hℓ1 hζi, sub_zero]
    rw [h0] at h
    exact h.mono_left (nhdsWithin_mono _ upperHalfDisc_subset_ball)

/-- **CONF Lemma 2.14, R1** (C:863, analytic form): for `0 < ℓ ≤ 1/10`, `g = l214Harm ℓ` is
harmonic on `𝔻`, `0 ≤ g ≤ 1` on the upper half-disc, `g((1 − ℓ) i) ≥ 1/(128π)`, and `g → 0`
at the boundary points of the upper half-disc at distance `≥ ℓ/4` from `c⁻`. -/
theorem l214_minorant {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1 / 10) :
    InnerProductSpace.HarmonicOnNhd (l214Harm ℓ) (ball (0 : ℂ) 1) ∧
    (∀ z ∈ upperHalfDisc, 0 ≤ l214Harm ℓ z ∧ l214Harm ℓ z ≤ 1) ∧
    1 / (128 * π) ≤ l214Harm ℓ (((1 - ℓ : ℝ) : ℂ) * I) ∧
    ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → 0 ≤ ζ.im → (‖ζ‖ = 1 ∨ ζ.im = 0) → ℓ / 4 ≤ ‖ζ - l214CenterM ℓ‖ →
      Tendsto (l214Harm ℓ) (𝓝[upperHalfDisc] ζ) (𝓝 0) :=
  ⟨harmonicOnNhd_l214Harm ℓ, fun _ hz => l214Harm_mem_Icc hℓ hℓ1 hz, l214Harm_ge hℓ hℓ1,
    fun _ h1 h2 h3 h4 => l214Harm_tendsto_zero hℓ hℓ1 h1 h2 h3 h4⟩

end CONF
end LQGMetric
