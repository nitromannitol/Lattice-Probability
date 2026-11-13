/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm12.Generator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.OnePointExpansion
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.TwoPointExpansion
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseHolo
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseFlow
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The short-time generator estimate in the proof of Theorem 1.2

Task GEN-PROB (`PLAN.md` §5 M2, step 3).

Setting: `σ : ℂ → ℝ` measurable, `|σ| ≤ M`, `σ = 0` outside `{δ ≤ Im z, ‖z‖ ≤ R}` (`δ > 0`).
For a continuous driver `W` and `f_r := revMap W r`:

* `Xs κ σ W s = ∫ σ z ((2/√κ) log ‖f_s z‖ + Qc(√κ) Re ∫_0^s 2/f_r(z)² dr) dz`,
* `Es σ W s = ∫∫ σ x σ y G(f_s x, f_s y) dx dy` with `G = neumannH`,
* `aW σ W r = ∫ σ z Re (1/f_r z) dz`.

Main results:

1. `energy_identity`: `Es σ W s - E0 σ = -4 ∫_0^s (aW σ W r)² dr` for `0 ≤ s ≤ 1`, where
   `E0 σ = ∫∫ σ x σ y G(x, y)` (the value at time `0`).
2. `norm_Psi_sub_le`: the generator estimate.
-/

noncomputable section

open Complex MeasureTheory Set Filter ProbabilityTheory
open scoped ComplexConjugate Topology NNReal

namespace QuantumZipper
namespace Generator

/-! ### Clamping into a closed half-plane, and joint continuity of the flow -/

/-- Projection onto the closed half-plane `{δ ≤ Im}`. -/
def clampH (δ : ℝ) (z : ℂ) : ℂ := (z.re : ℂ) + ((max z.im δ : ℝ) : ℂ) * I

lemma clampH_im (δ : ℝ) (z : ℂ) : (clampH δ z).im = max z.im δ := by
  simp [clampH]

lemma clampH_im_ge (δ : ℝ) (z : ℂ) : δ ≤ (clampH δ z).im := by
  rw [clampH_im]; exact le_max_right _ _

lemma clampH_of_le {δ : ℝ} {z : ℂ} (h : δ ≤ z.im) : clampH δ z = z := by
  apply Complex.ext <;> simp [clampH, max_eq_left h]

lemma continuous_clampH (δ : ℝ) : Continuous (clampH δ) := by
  unfold clampH; fun_prop

/-- The flow evaluated at clamped time and clamped point; jointly continuous. -/
def revF (W : ℝ → ℝ) (δ : ℝ) (r : ℝ) (z : ℂ) : ℂ := revMap W (max r 0) (clampH δ z)

lemma revF_eq {W : ℝ → ℝ} {δ r : ℝ} {z : ℂ} (hr : 0 ≤ r) (hz : δ ≤ z.im) :
    revF W δ r z = revMap W r z := by
  simp [revF, max_eq_left hr, clampH_of_le hz]

lemma revF_im_ge {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (z : ℂ) :
    δ ≤ (revF W δ r z).im :=
  TwoPointExp.le_im_revMap' hW hδ (clampH_im_ge δ z) (le_max_right r 0)

lemma revF_norm_ge {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (z : ℂ) :
    δ ≤ ‖revF W δ r z‖ :=
  (revF_im_ge hW hδ r z).trans (Complex.im_le_norm _)

lemma revF_ne_zero {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (z : ℂ) :
    revF W δ r z ≠ 0 :=
  norm_pos_iff.mp (hδ.trans_le (revF_norm_ge hW hδ r z))

theorem continuous_revF {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : ℝ × ℂ => revF W δ p.1 p.2) := by
  have htime : ∀ z : ℂ, Continuous (fun r : ℝ => revF W δ r z) := fun z =>
    (ReverseFlow.continuousOn_revMap_time W hW (clampH δ z)
      (hδ.trans_le (clampH_im_ge δ z))).comp_continuous
      (continuous_id.max continuous_const) (fun r => le_max_right r 0)
  rw [continuous_iff_continuousAt]
  rintro ⟨r0, z0⟩
  set L := Real.exp (2 * (|r0| + 1) / δ ^ 2)
  have hbound : ∀ᶠ p : ℝ × ℂ in 𝓝 (r0, z0),
      ‖revF W δ p.1 p.2 - revF W δ r0 z0‖ ≤
        ‖clampH δ p.2 - clampH δ z0‖ * L + ‖revF W δ p.1 z0 - revF W δ r0 z0‖ := by
    have hev : ∀ᶠ p : ℝ × ℂ in 𝓝 (r0, z0), |p.1 - r0| < 1 := by
      have hc : Continuous (fun p : ℝ × ℂ => |p.1 - r0|) := by fun_prop
      exact hc.continuousAt.eventually (gt_mem_nhds (by simp))
    filter_upwards [hev] with p hp
    have h1 : ‖revF W δ p.1 p.2 - revF W δ p.1 z0‖ ≤
        ‖clampH δ p.2 - clampH δ z0‖ * Real.exp (2 * max p.1 0 / δ ^ 2) :=
      ReverseFlow.norm_revMap_sub_revMap_point W hW hδ (clampH_im_ge δ p.2)
        (clampH_im_ge δ z0) (le_max_right p.1 0)
    have hT : max p.1 0 ≤ |r0| + 1 := by
      rw [max_le_iff]; constructor
      · linarith [le_abs_self r0, (abs_lt.mp hp).2]
      · positivity
    have hE : Real.exp (2 * max p.1 0 / δ ^ 2) ≤ L := Real.exp_le_exp.mpr (by gcongr)
    calc ‖revF W δ p.1 p.2 - revF W δ r0 z0‖
        ≤ ‖revF W δ p.1 p.2 - revF W δ p.1 z0‖ + ‖revF W δ p.1 z0 - revF W δ r0 z0‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left hE (norm_nonneg _))
  have hlim : Tendsto (fun p : ℝ × ℂ => ‖clampH δ p.2 - clampH δ z0‖ * L +
      ‖revF W δ p.1 z0 - revF W δ r0 z0‖) (𝓝 (r0, z0)) (𝓝 0) := by
    have h1 := htime z0
    have h2 := continuous_clampH δ
    have hc : Continuous (fun p : ℝ × ℂ => ‖clampH δ p.2 - clampH δ z0‖ * L +
        ‖revF W δ p.1 z0 - revF W δ r0 z0‖) := by fun_prop
    simpa using hc.tendsto (r0, z0)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

/-! ### The derivative of the Neumann kernel along the flow -/

theorem hasDerivAt_log_norm {D : ℝ → ℂ} {D' : ℂ} {t : ℝ} (hD : HasDerivAt D D' t)
    (h0 : D t ≠ 0) : HasDerivAt (fun τ => Real.log ‖D τ‖) (D' / D t).re t := by
  have h1 := hD.norm_sq
  have hpos : 0 < ‖D t‖ ^ 2 := by positivity
  have h3 := (h1.log hpos.ne').div_const 2
  have heq : (fun τ => Real.log (‖D τ‖ ^ 2) / 2) = fun τ => Real.log ‖D τ‖ := by
    funext τ; rw [Real.log_pow]; push_cast; ring
  rw [heq] at h3
  refine h3.congr_deriv ?_
  symm
  rw [Complex.inner, Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  have : (D t).re * (D t).re + (D t).im * (D t).im ≠ 0 := by
    rw [← Complex.normSq_apply]; exact (Complex.normSq_pos.mpr h0).ne'
  field_simp
  ring

lemma neumann_deriv_algebra {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (h1 : u - v ≠ 0)
    (h2 : u - conj v ≠ 0) :
    -((-2 / u - -2 / v) / (u - v)).re - ((-2 / u - conj (-2 / v)) / (u - conj v)).re =
      -4 * ((1 / u).re * (1 / v).re) := by
  have hcv : conj v ≠ 0 := (map_ne_zero _).mpr hv
  have e1 : (-2 / u - -2 / v) / (u - v) = 2 * ((1 / u) * (1 / v)) := by
    field_simp; ring
  have e2 : (-2 / u - conj (-2 / v)) / (u - conj v) = 2 * ((1 / u) * conj (1 / v)) := by
    simp only [map_div₀, map_neg, map_ofNat, map_one]
    field_simp; ring
  rw [e1, e2]
  have e3 : (1 / u) * (1 / v) + (1 / u) * conj (1 / v) = (1 / u) * (((2 * (1 / v).re : ℝ)) : ℂ) := by
    rw [← mul_add, Complex.add_conj]
  have e4 : (2 * ((1 / u) * (1 / v))).re + (2 * ((1 / u) * conj (1 / v))).re =
      2 * ((1 / u) * (1 / v) + (1 / u) * conj (1 / v)).re := by
    have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
    rw [h2re, h2re, Complex.add_re]; ring
  have e5 : ((1 / u) * (((2 * (1 / v).re : ℝ)) : ℂ)).re = (1 / u).re * (2 * (1 / v).re) :=
    Complex.re_mul_ofReal _ _
  linarith [e4, congrArg Complex.re e3, e5]

/-- **Pointwise energy identity.** For `x ≠ y` in `ℍ`,
`G(f_s x, f_s y) - G(x, y) = ∫_0^s -4 Re(1/f_r x) Re(1/f_r y) dr`. -/
theorem neumannH_revMap_sub_eq {W : ℝ → ℝ} (hW : Continuous W) {x y : ℂ} (hx : 0 < x.im)
    (hy : 0 < y.im) (hxy : x ≠ y) {s : ℝ} (hs : 0 ≤ s) :
    neumannH (revMap W s x) (revMap W s y) - neumannH x y =
      ∫ r in (0 : ℝ)..s, -4 * ((1 / revMap W r x).re * (1 / revMap W r y).re) := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW x hx s hs
  obtain ⟨v, hv⟩ := exists_isReverseSol W hW y hy s hs
  have hue : ∀ r ∈ Icc 0 s, revMap W r x = u r := fun r hr => revMap_eq W hW x hr.1 hr.2 hu
  have hve : ∀ r ∈ Icc 0 s, revMap W r y = v r := fun r hr => revMap_eq W hW y hr.1 hr.2 hv
  have hupos : ∀ r ∈ Icc 0 s, 0 < (u r).im := fun r hr => (hu.2 r hr).1
  have hvpos : ∀ r ∈ Icc 0 s, 0 < (v r).im := fun r hr => (hv.2 r hr).1
  have hu0 : ∀ r ∈ Icc 0 s, u r ≠ 0 := fun r hr h => by
    have := hupos r hr; rw [h] at this; simp at this
  have hv0 : ∀ r ∈ Icc 0 s, v r ≠ 0 := fun r hr h => by
    have := hvpos r hr; rw [h] at this; simp at this
  have hne1 : ∀ r ∈ Icc 0 s, u r - v r ≠ 0 := by
    intro r hr h
    have h' : revMap W r x = revMap W r y := by rw [hue r hr, hve r hr]; exact sub_eq_zero.mp h
    exact hxy (injOn_revMap W hW hr.1 hx hy h')
  have hne2 : ∀ r ∈ Icc 0 s, u r - conj (v r) ≠ 0 := by
    intro r hr h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith [hupos r hr, hvpos r hr]
  have hcont : ContinuousOn (fun t => neumannH (u t) (v t)) (Icc 0 s) := by
    unfold neumannH
    refine ContinuousOn.sub (ContinuousOn.neg ?_) ?_
    · exact ((hu.1.sub hv.1).norm).log fun t ht => norm_ne_zero_iff.mpr (hne1 t ht)
    · exact ((hu.1.sub (Complex.continuous_conj.comp_continuousOn hv.1)).norm).log
        fun t ht => norm_ne_zero_iff.mpr (hne2 t ht)
  have hderiv : ∀ t ∈ Ioo 0 s, HasDerivAt (fun t => neumannH (u t) (v t))
      (-4 * ((1 / u t).re * (1 / v t).re)) t := by
    intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hdu := (isReverseSol_hasDerivWithinAt W x s hu ht').hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hdv := (isReverseSol_hasDerivWithinAt W y s hv ht').hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hD1 : HasDerivAt (fun r => u r - v r) (-2 / u t - -2 / v t) t :=
      (hdu.sub hdv).congr_of_eventuallyEq
        (Eventually.of_forall fun r => by simp only [Pi.sub_apply]; ring)
    have hD2 : HasDerivAt (fun r => u r - conj (v r)) (-2 / u t - conj (-2 / v t)) t :=
      (hdu.sub hdv.star).congr_of_eventuallyEq
        (Eventually.of_forall fun r => by
          simp only [Pi.sub_apply, star_add, Complex.star_def, Complex.conj_ofReal]; ring)
    have hL1 := hasDerivAt_log_norm hD1 (hne1 t ht')
    have hL2 := hasDerivAt_log_norm hD2 (hne2 t ht')
    have := hL1.neg.sub hL2
    rw [← neumann_deriv_algebra (hu0 t ht') (hv0 t ht') (hne1 t ht') (hne2 t ht')]
    exact this
  have hint : IntervalIntegrable (fun t => -4 * ((1 / u t).re * (1 / v t).re)) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs]
    have hcu : ContinuousOn (fun t => (1 / u t).re) (Icc 0 s) :=
      Complex.continuous_re.comp_continuousOn (continuousOn_const.div hu.1 hu0)
    have hcv : ContinuousOn (fun t => (1 / v t).re) (Icc 0 s) :=
      Complex.continuous_re.comp_continuousOn (continuousOn_const.div hv.1 hv0)
    exact continuousOn_const.mul (hcu.mul hcv)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hcont hderiv hint
  have hu00 : u 0 = x - W 0 := by rw [(hu.2 0 ⟨le_rfl, hs⟩).2]; simp
  have hv00 : v 0 = y - W 0 := by rw [(hv.2 0 ⟨le_rfl, hs⟩).2]; simp
  have hG0 : neumannH (u 0) (v 0) = neumannH x y := by
    rw [hu00, hv00]
    simp only [neumannH, map_sub, Complex.conj_ofReal, sub_sub_sub_cancel_right]
  rw [hue s ⟨hs, le_rfl⟩, hve s ⟨hs, le_rfl⟩, ← hG0, ← key]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs] at hr
  simp only [hue r hr, hve r hr]

/-! ### Standing hypotheses on the test function -/

/-- Standing hypotheses: `σ` measurable, `|σ| ≤ M`, and `σ = 0` outside
`{z | δ ≤ z.im ∧ ‖z‖ ≤ R}`, with `δ > 0`. -/
structure IsGenTest (σ : ℂ → ℝ) (δ R M : ℝ) : Prop where
  pos : 0 < δ
  meas : Measurable σ
  bound : ∀ z, |σ z| ≤ M
  supp : ∀ z, σ z ≠ 0 → δ ≤ z.im ∧ ‖z‖ ≤ R

/-- `‖σ‖₁ = ∫ |σ|`. -/
def N1 (σ : ℂ → ℝ) : ℝ := ∫ z, |σ z|

lemma N1_nonneg (σ : ℂ → ℝ) : 0 ≤ N1 σ := integral_nonneg fun _ => abs_nonneg _

variable {σ : ℂ → ℝ} {δ R M : ℝ}

namespace IsGenTest

lemma M_nonneg (h : IsGenTest σ δ R M) : 0 ≤ M := (abs_nonneg _).trans (h.bound 0)

lemma mul_congr (h : IsGenTest σ δ R M) {g g' : ℂ → ℝ}
    (hg : ∀ z, δ ≤ z.im → ‖z‖ ≤ R → g z = g' z) :
    (fun z => σ z * g z) = fun z => σ z * g' z := by
  funext z
  by_cases hz : σ z = 0
  · simp [hz]
  · obtain ⟨h1, h2⟩ := h.supp z hz; rw [hg z h1 h2]

lemma integrable_mul (h : IsGenTest σ δ R M) {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume)
    {C : ℝ} (hC : 0 ≤ C) (hgC : ∀ z, δ ≤ z.im → ‖z‖ ≤ R → |g z| ≤ C) :
    Integrable (fun z => σ z * g z) := by
  refine Integrable.mono' (g := (Metric.closedBall (0 : ℂ) R).indicator (fun _ => M * C))
    ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)) (h.meas.aestronglyMeasurable.mul hg) ?_
  refine Eventually.of_forall fun z => ?_
  by_cases hz : σ z = 0
  · simp only [hz, zero_mul, norm_zero]
    exact indicator_nonneg (fun _ _ => mul_nonneg h.M_nonneg hC) z
  · obtain ⟨h1, h2⟩ := h.supp z hz
    rw [indicator_of_mem (by simpa using h2), Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (h.bound z) (hgC z h1 h2) (abs_nonneg _) h.M_nonneg

lemma integrable (h : IsGenTest σ δ R M) : Integrable σ := by
  simpa using h.integrable_mul (g := fun _ => 1) aestronglyMeasurable_const zero_le_one
    (fun _ _ _ => by simp)

lemma abs_integral_mul_le (h : IsGenTest σ δ R M) {g : ℂ → ℝ} {C : ℝ}
    (hgC : ∀ z, δ ≤ z.im → ‖z‖ ≤ R → |g z| ≤ C) : |∫ z, σ z * g z| ≤ C * N1 σ := by
  have hpt : ∀ z, ‖σ z * g z‖ ≤ C * |σ z| := by
    intro z
    by_cases hz : σ z = 0
    · simp [hz]
    · obtain ⟨h1, h2⟩ := h.supp z hz
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hgC z h1 h2) (abs_nonneg _)
  have := norm_integral_le_of_norm_le (h.integrable.abs.const_mul C) (Eventually.of_forall hpt)
  rw [integral_const_mul, Real.norm_eq_abs] at this
  exact this

end IsGenTest

/-! ### The energy functional -/

/-- The variance functional `E_s(σ) = ∫∫ σ(x) σ(y) G(f_s x, f_s y)`. -/
def Es (σ : ℂ → ℝ) (W : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x, ∫ y, σ x * σ y * neumannH (revMap W s x) (revMap W s y)

/-- The time-zero energy `E_0(σ) = ∫∫ σ(x) σ(y) G(x, y)`. -/
def E0 (σ : ℂ → ℝ) : ℝ := ∫ x, ∫ y, σ x * σ y * neumannH x y

/-- `a_r = ∫ σ(z) Re(1/f_r z) dz`. -/
def aW (σ : ℂ → ℝ) (W : ℝ → ℝ) (r : ℝ) : ℝ := ∫ z, σ z * (1 / revMap W r z).re

/-- `a = ∫ σ(z) Re(1/z) dz`. -/
def a0 (σ : ℂ → ℝ) : ℝ := ∫ z, σ z * (1 / z).re

lemma integrable_logNeg : Integrable (fun y : ℂ => max (-Real.log ‖y‖) 0) := by
  refine ⟨(((Real.measurable_log.comp continuous_norm.measurable).neg).max
    measurable_const).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq ?_) admissible_lintegral_logNeg_lt_top
  refine lintegral_congr fun y => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (le_max_right _ _)]
  rcases le_total (-Real.log ‖y‖) 0 with hy | hy
  · rw [max_eq_right hy, ENNReal.ofReal_of_nonpos hy, ENNReal.ofReal_zero]
  · rw [max_eq_left hy]

lemma abs_log_le_logNeg_add {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hT : 1 ≤ T) :
    |Real.log t| ≤ max (-Real.log t) 0 + Real.log T := by
  have hT0 := Real.log_nonneg hT
  rcases le_or_gt t 1 with h1 | h1
  · have := Real.log_nonpos ht h1
    rw [abs_of_nonpos this]; linarith [le_max_left (-Real.log t) 0]
  · have hp : 0 < Real.log t := Real.log_pos h1
    rw [abs_of_pos hp]
    linarith [Real.log_le_log (by linarith) htT, le_max_right (-Real.log t) 0]

lemma IsGenTest.integrable_prod_log (h : IsGenTest σ δ R M) {H : ℂ × ℂ → ℝ}
    (hHm : AEStronglyMeasurable H ((volume : Measure ℂ).prod volume)) {C : ℝ} (hC : 0 ≤ C)
    (hHb : ∀ x y : ℂ, δ ≤ x.im → ‖x‖ ≤ R → δ ≤ y.im → ‖y‖ ≤ R →
      |H (x, y)| ≤ |Real.log ‖x - y‖| + C) :
    Integrable (fun p : ℂ × ℂ => σ p.1 * σ p.2 * H p) ((volume : Measure ℂ).prod volume) := by
  set B := Metric.closedBall (0 : ℂ) R
  set Λ : ℂ → ℝ := fun y => max (-Real.log ‖y‖) 0 with hΛdef
  set ι : ℂ → ℝ := B.indicator fun _ => (1 : ℝ) with hιdef
  have hΛm : Measurable Λ :=
    ((Real.measurable_log.comp continuous_norm.measurable).neg).max measurable_const
  have hιm : Measurable ι := measurable_const.indicator measurableSet_closedBall
  have hι0 : ∀ x, 0 ≤ ι x := fun x => indicator_nonneg (fun _ _ => zero_le_one) x
  have hB : Integrable ι := (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const measure_closedBall_lt_top.ne)
  have hg1 : Integrable (fun p : ℂ × ℂ => ι p.1 * Λ (p.2 - p.1))
      ((volume : Measure ℂ).prod volume) := by
    have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => ι p.1 * Λ (p.2 - p.1))
        ((volume : Measure ℂ).prod volume) :=
      ((hιm.comp measurable_fst).mul (hΛm.comp (measurable_snd.sub measurable_fst))).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact (integrable_logNeg.comp_sub_right x).const_mul (ι x)
    have : (fun x => ∫ y, ‖ι x * Λ (y - x)‖) = fun x => ι x * ∫ y, Λ y := by
      funext x
      have e : (fun y => ‖ι x * Λ (y - x)‖) = fun y => ι x * Λ (y - x) := by
        funext y
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hι0 x) (le_max_right _ _))]
      rw [e, integral_const_mul, integral_sub_right_eq_self (fun y => Λ y) x]
    rw [this]; exact hB.mul_const _
  have hg2 : Integrable (fun p : ℂ × ℂ => ι p.1 * ι p.2) ((volume : Measure ℂ).prod volume) :=
    hB.mul_prod hB
  have hL : 0 ≤ Real.log (2 * |R| + 1) := Real.log_nonneg (by linarith [abs_nonneg R])
  have hgnn : ∀ p : ℂ × ℂ, 0 ≤ M ^ 2 * (ι p.1 * Λ (p.2 - p.1)) +
      M ^ 2 * (Real.log (2 * |R| + 1) + C) * (ι p.1 * ι p.2) := fun p =>
    add_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (hι0 _) (le_max_right _ _)))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (add_nonneg hL hC)) (mul_nonneg (hι0 _) (hι0 _)))
  refine Integrable.mono' ((hg1.const_mul (M ^ 2)).add
    (hg2.const_mul (M ^ 2 * (Real.log (2 * |R| + 1) + C))))
    (((h.meas.comp measurable_fst).aestronglyMeasurable.mul
      (h.meas.comp measurable_snd).aestronglyMeasurable).mul hHm) ?_
  refine Eventually.of_forall fun p => ?_
  obtain ⟨x, y⟩ := p
  by_cases hxy : σ x = 0 ∨ σ y = 0
  · have : σ x * σ y * H (x, y) = 0 := by rcases hxy with hx | hx <;> simp [hx]
    rw [this, norm_zero]; exact hgnn _
  · push Not at hxy
    show ‖σ x * σ y * H (x, y)‖ ≤ M ^ 2 * (ι x * Λ (y - x)) +
      M ^ 2 * (Real.log (2 * |R| + 1) + C) * (ι x * ι y)
    obtain ⟨hx1, hx2⟩ := h.supp x hxy.1
    obtain ⟨hy1, hy2⟩ := h.supp y hxy.2
    have hxB : ι x = 1 := indicator_of_mem (by simpa [B] using hx2) _
    have hyB : ι y = 1 := indicator_of_mem (by simpa [B] using hy2) _
    simp only [hxB, hyB, mul_one, one_mul]
    have hd : ‖x - y‖ ≤ 2 * |R| + 1 := by
      linarith [norm_sub_le x y, le_abs_self R]
    have hlog := abs_log_le_logNeg_add (norm_nonneg (x - y)) hd (by linarith [abs_nonneg R])
    have hΛ : Λ (y - x) = max (-Real.log ‖x - y‖) 0 := by simp [hΛdef, norm_sub_rev]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, hΛ]
    have hσσ : |σ x| * |σ y| ≤ M ^ 2 := by
      rw [sq]; exact mul_le_mul (h.bound x) (h.bound y) (abs_nonneg _) h.M_nonneg
    have hH := hHb x y hx1 hx2 hy1 hy2
    calc |σ x| * |σ y| * |H (x, y)|
        ≤ M ^ 2 * (max (-Real.log ‖x - y‖) 0 + Real.log (2 * |R| + 1) + C) :=
          mul_le_mul hσσ (by linarith) (abs_nonneg _) (sq_nonneg _)
      _ = _ := by ring

lemma measurable_neumannH : Measurable (fun p : ℂ × ℂ => neumannH p.1 p.2) := by
  unfold neumannH
  exact ((Real.measurable_log.comp (continuous_fst.sub continuous_snd).norm.measurable).neg).sub
    (Real.measurable_log.comp
      (continuous_fst.sub (Complex.continuous_conj.comp continuous_snd)).norm.measurable)

lemma Es_integrand_eq (h : IsGenTest σ δ R M) {W : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) (p : ℂ × ℂ) :
    σ p.1 * σ p.2 * neumannH (revMap W s p.1) (revMap W s p.2) =
      σ p.1 * σ p.2 * neumannH (revF W δ s p.1) (revF W δ s p.2) := by
  by_cases hxy : σ p.1 = 0 ∨ σ p.2 = 0
  · rcases hxy with hx | hx <;> simp [hx]
  · push Not at hxy
    rw [revF_eq hs (h.supp _ hxy.1).1, revF_eq hs (h.supp _ hxy.2).1]

lemma integrable_Es_integrand (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Integrable (fun p : ℂ × ℂ => σ p.1 * σ p.2 * neumannH (revMap W s p.1) (revMap W s p.2))
      ((volume : Measure ℂ).prod volume) := by
  have hcF := continuous_revF hW h.pos
  have hc1 : Continuous (fun p : ℂ × ℂ => revF W δ s p.1) :=
    hcF.comp (continuous_const.prodMk continuous_fst)
  have hc2 : Continuous (fun p : ℂ × ℂ => revF W δ s p.2) :=
    hcF.comp (continuous_const.prodMk continuous_snd)
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => neumannH (revF W δ s p.1) (revF W δ s p.2))
      ((volume : Measure ℂ).prod volume) :=
    (measurable_neumannH.comp (hc1.measurable.prodMk hc2.measurable)).aestronglyMeasurable
  have hC : 0 ≤ TwoPointExp.tpeCrude δ R := by unfold TwoPointExp.tpeCrude; positivity
  have := h.integrable_prod_log hm hC (fun x y hx1 hx2 hy1 hy2 => by
    show |neumannH (revF W δ s x) (revF W δ s y)| ≤ _
    rw [revF_eq hs hx1, revF_eq hs hy1]
    exact TwoPointExp.abs_neumannH_revMap_le hW h.pos hx1 hy1 hx2 hy2 hs hs1)
  exact this.congr (Eventually.of_forall fun p => (Es_integrand_eq h hs p).symm)

lemma Es_eq_integral_prod (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Es σ W s = ∫ p, σ p.1 * σ p.2 * neumannH (revMap W s p.1) (revMap W s p.2)
      ∂((volume : Measure ℂ).prod volume) :=
  (integral_prod _ (integrable_Es_integrand h hW hs hs1)).symm

lemma neumannH_revMap_zero {W : ℝ → ℝ} (hW : Continuous W) {x y : ℂ} (hx : 0 < x.im)
    (hy : 0 < y.im) : neumannH (revMap W 0 x) (revMap W 0 y) = neumannH x y := by
  rw [TwoPointExp.revMap_eq_sub_drift hW hx le_rfl, TwoPointExp.revMap_eq_sub_drift hW hy le_rfl]
  simp only [TwoPointExp.revDrift, intervalIntegral.integral_same, sub_zero, neumannH, map_sub,
    Complex.conj_ofReal, sub_sub_sub_cancel_right]

lemma Es_zero (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) : Es σ W 0 = E0 σ := by
  unfold Es E0
  congr 1; funext x; congr 1; funext y
  by_cases hxy : σ x = 0 ∨ σ y = 0
  · rcases hxy with hx | hx <;> simp [hx]
  · push Not at hxy
    rw [neumannH_revMap_zero hW (h.pos.trans_le (h.supp x hxy.1).1)
      (h.pos.trans_le (h.supp y hxy.2).1)]

/-- `Re (1 / f_r z)` evaluated through the clamped flow. -/
def hFun (W : ℝ → ℝ) (δ : ℝ) (r : ℝ) (z : ℂ) : ℝ := (1 / revF W δ r z).re

lemma continuous_hFun {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : ℝ × ℂ => hFun W δ p.1 p.2) :=
  Complex.continuous_re.comp (continuous_const.div (continuous_revF hW hδ)
    (fun p => revF_ne_zero hW hδ p.1 p.2))

lemma continuous_revF_time {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    Continuous (fun r : ℝ => revF W δ r z) :=
  (ReverseFlow.continuousOn_revMap_time W hW (clampH δ z)
    (hδ.trans_le (clampH_im_ge δ z))).comp_continuous
    (continuous_id.max continuous_const) (fun r => le_max_right r 0)

lemma continuous_hFun_time {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    Continuous (fun r : ℝ => hFun W δ r z) :=
  Complex.continuous_re.comp (continuous_const.div (continuous_revF_time hW hδ z)
    (fun r => revF_ne_zero hW hδ r z))

lemma abs_hFun_le {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (z : ℂ) :
    |hFun W δ r z| ≤ 1 / δ :=
  (Complex.abs_re_le_norm _).trans (OnePointExpansion.norm_one_div_le hδ (revF_norm_ge hW hδ r z))

lemma hFun_eq {W : ℝ → ℝ} {δ r : ℝ} {z : ℂ} (hr : 0 ≤ r) (hz : δ ≤ z.im) :
    hFun W δ r z = (1 / revMap W r z).re := by
  rw [hFun, revF_eq hr hz]

lemma energy_swap_integrable (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ}
    (hs : 0 ≤ s) :
    Integrable (fun q : ℝ × (ℂ × ℂ) =>
      -4 * (σ q.2.1 * hFun W δ q.1 q.2.1) * (σ q.2.2 * hFun W δ q.1 q.2.2))
      ((volume.restrict (uIoc (0 : ℝ) s)).prod ((volume : Measure ℂ).prod volume)) := by
  have hδ := h.pos
  have hIfin : (volume : Measure ℝ) (uIoc 0 s) ≠ ⊤ := by
    rw [uIoc_of_le hs, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  set ι : ℂ → ℝ := (Metric.closedBall (0 : ℂ) R).indicator fun _ => (1 : ℝ) with hιdef
  have hB : Integrable ι :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  have hind0 : ∀ z, 0 ≤ ι z := fun z => indicator_nonneg (fun _ _ => zero_le_one) z
  have hdom : Integrable (fun q : ℝ × (ℂ × ℂ) => (4 * (M / δ) ^ 2) * (ι q.2.1 * ι q.2.2))
      ((volume.restrict (uIoc (0 : ℝ) s)).prod ((volume : Measure ℂ).prod volume)) :=
    (show Integrable (fun _ : ℝ => (4 * (M / δ) ^ 2)) (volume.restrict (uIoc (0 : ℝ) s)) from
      integrableOn_const hIfin).mul_prod (hB.mul_prod hB)
  have hc := continuous_hFun hW hδ
  have m1 : Measurable (fun q : ℝ × (ℂ × ℂ) => hFun W δ q.1 q.2.1) :=
    (hc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).measurable
  have m2 : Measurable (fun q : ℝ × (ℂ × ℂ) => hFun W δ q.1 q.2.2) :=
    (hc.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).measurable
  have m3 : Measurable (fun q : ℝ × (ℂ × ℂ) => σ q.2.1) :=
    h.meas.comp (measurable_fst.comp measurable_snd)
  have m4 : Measurable (fun q : ℝ × (ℂ × ℂ) => σ q.2.2) :=
    h.meas.comp (measurable_snd.comp measurable_snd)
  refine hdom.mono' ((measurable_const.mul (m3.mul m1)).mul (m4.mul m2)).aestronglyMeasurable
    (Eventually.of_forall fun q => ?_)
  obtain ⟨r, x, y⟩ := q
  show ‖-4 * (σ x * hFun W δ r x) * (σ y * hFun W δ r y)‖ ≤ 4 * (M / δ) ^ 2 * (ι x * ι y)
  by_cases hxy : σ x = 0 ∨ σ y = 0
  · have : -4 * (σ x * hFun W δ r x) * (σ y * hFun W δ r y) = 0 := by
      rcases hxy with hx | hx <;> simp [hx]
    rw [this, norm_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hind0 _) (hind0 _))
  · push Not at hxy
    obtain ⟨_, hx2⟩ := h.supp x hxy.1
    obtain ⟨_, hy2⟩ := h.supp y hxy.2
    have hxB : ι x = 1 := indicator_of_mem (by simpa using hx2) _
    have hyB : ι y = 1 := indicator_of_mem (by simpa using hy2) _
    rw [hxB, hyB]
    have e1 : |σ x * hFun W δ r x| ≤ M / δ := by
      rw [abs_mul, div_eq_mul_one_div]
      exact mul_le_mul (h.bound x) (abs_hFun_le hW hδ r x) (abs_nonneg _) h.M_nonneg
    have e2 : |σ y * hFun W δ r y| ≤ M / δ := by
      rw [abs_mul, div_eq_mul_one_div]
      exact mul_le_mul (h.bound y) (abs_hFun_le hW hδ r y) (abs_nonneg _) h.M_nonneg
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hMδ : 0 ≤ M / δ := div_nonneg h.M_nonneg hδ.le
    calc 4 * |σ x * hFun W δ r x| * |σ y * hFun W δ r y| ≤ 4 * (M / δ) * (M / δ) := by gcongr
      _ = _ := by ring

lemma ae_ne_prod : ∀ᵐ p ∂((volume : Measure ℂ).prod volume), p ∈ ({q : ℂ × ℂ | q.1 = q.2})ᶜ := by
  rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_eq_fun measurable_fst measurable_snd).compl]
  refine Eventually.of_forall fun x => ?_
  refine measure_mono_null (fun y hy => ?_) (measure_singleton x)
  simp only [mem_compl_iff, Set.mem_ofPred_eq, not_not] at hy
  exact hy.symm

lemma aW_eq_integral_hFun (h : IsGenTest σ δ R M) {W : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    aW σ W r = ∫ z, σ z * hFun W δ r z := by
  unfold aW
  rw [h.mul_congr (g := fun z => (1 / revMap W r z).re) (g' := fun z => hFun W δ r z)
    (fun z hz1 _ => (hFun_eq hr hz1).symm)]

/-- **Energy identity.** For `0 ≤ s ≤ 1`, `E_s - E_0 = -4 ∫_0^s a_r² dr`. -/
theorem energy_identity (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Es σ W s - Es σ W 0 = -4 * ∫ r in (0 : ℝ)..s, aW σ W r ^ 2 := by
  have hδ := h.pos
  have step1 : Es σ W s - Es σ W 0 = ∫ p, (σ p.1 * σ p.2 * neumannH (revMap W s p.1) (revMap W s p.2)
      - σ p.1 * σ p.2 * neumannH (revMap W 0 p.1) (revMap W 0 p.2))
        ∂((volume : Measure ℂ).prod volume) := by
    rw [Es_eq_integral_prod h hW hs hs1, Es_eq_integral_prod h hW le_rfl zero_le_one,
      integral_sub (integrable_Es_integrand h hW hs hs1)
        (integrable_Es_integrand h hW le_rfl zero_le_one)]
  have step2 : ∫ p, (σ p.1 * σ p.2 * neumannH (revMap W s p.1) (revMap W s p.2)
      - σ p.1 * σ p.2 * neumannH (revMap W 0 p.1) (revMap W 0 p.2))
        ∂((volume : Measure ℂ).prod volume)
      = ∫ p, (∫ r in (0 : ℝ)..s,
          -4 * (σ p.1 * hFun W δ r p.1) * (σ p.2 * hFun W δ r p.2))
        ∂((volume : Measure ℂ).prod volume) := by
    refine integral_congr_ae (ae_ne_prod.mono fun p hp => ?_)
    obtain ⟨x, y⟩ := p
    have hp' : x ≠ y := by simpa using hp
    by_cases hxy : σ x = 0 ∨ σ y = 0
    · rcases hxy with hx | hx <;> simp [hx]
    · push Not at hxy
      obtain ⟨hx1, _⟩ := h.supp x hxy.1
      obtain ⟨hy1, _⟩ := h.supp y hxy.2
      have hxp : 0 < x.im := hδ.trans_le hx1
      have hyp : 0 < y.im := hδ.trans_le hy1
      show σ x * σ y * neumannH (revMap W s x) (revMap W s y) -
          σ x * σ y * neumannH (revMap W 0 x) (revMap W 0 y) =
        ∫ r in (0 : ℝ)..s, -4 * (σ x * hFun W δ r x) * (σ y * hFun W δ r y)
      rw [← mul_sub, neumannH_revMap_zero hW hxp hyp, neumannH_revMap_sub_eq hW hxp hyp hp' hs,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs] at hr
      simp only [hFun_eq hr.1 hx1, hFun_eq hr.1 hy1]
      ring
  have step3 : ∫ p, (∫ r in (0 : ℝ)..s,
          -4 * (σ p.1 * hFun W δ r p.1) * (σ p.2 * hFun W δ r p.2))
        ∂((volume : Measure ℂ).prod volume) =
      ∫ r in (0 : ℝ)..s, ∫ p, -4 * (σ p.1 * hFun W δ r p.1) * (σ p.2 * hFun W δ r p.2)
        ∂((volume : Measure ℂ).prod volume) :=
    (intervalIntegral_integral_swap (energy_swap_integrable h hW hs)).symm
  have step4 : ∀ r, 0 ≤ r → ∫ p, -4 * (σ p.1 * hFun W δ r p.1) * (σ p.2 * hFun W δ r p.2)
      ∂((volume : Measure ℂ).prod volume) = -4 * aW σ W r ^ 2 := by
    intro r hr
    have e : (fun p : ℂ × ℂ => -4 * (σ p.1 * hFun W δ r p.1) * (σ p.2 * hFun W δ r p.2)) =
        fun p => -4 * ((σ p.1 * hFun W δ r p.1) * (σ p.2 * hFun W δ r p.2)) := by
      funext p; ring
    rw [e, integral_const_mul, integral_prod_mul (fun z => σ z * hFun W δ r z)
      (fun z => σ z * hFun W δ r z), ← aW_eq_integral_hFun h hr, sq]
  rw [step1, step2, step3, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs] at hr
  exact step4 r hr.1

/-! ### Consequences of the energy identity -/

lemma abs_aW_le (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {r : ℝ} (hr : 0 ≤ r) :
    |aW σ W r| ≤ 1 / δ * N1 σ := by
  rw [aW_eq_integral_hFun h hr]
  exact h.abs_integral_mul_le (fun z _ _ => abs_hFun_le hW h.pos r z)

lemma measurable_one_div_re : Measurable (fun z : ℂ => (1 / z).re) := by
  simp only [one_div]; exact Complex.measurable_re.comp measurable_inv

lemma measurable_one_div_sq_re : Measurable (fun z : ℂ => (1 / z ^ 2).re) := by
  simp only [one_div]; exact Complex.measurable_re.comp ((measurable_id.pow_const 2).inv)

lemma abs_one_div_re_le {z : ℂ} (hz : δ ≤ z.im) (hδ : 0 < δ) : |(1 / z).re| ≤ 1 / δ :=
  (Complex.abs_re_le_norm _).trans
    (OnePointExpansion.norm_one_div_le hδ (hz.trans (Complex.im_le_norm z)))

lemma abs_a0_le (h : IsGenTest σ δ R M) : |a0 σ| ≤ 1 / δ * N1 σ :=
  h.abs_integral_mul_le (fun _ hz1 _ => abs_one_div_re_le hz1 h.pos)

lemma continuous_aF (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) :
    Continuous (fun r => ∫ z, σ z * hFun W δ r z) := by
  refine continuous_of_dominated (F := fun r z => σ z * hFun W δ r z)
    (bound := fun z => |σ z| * (1 / δ)) (fun r => ?_) (fun r => ?_)
    (h.integrable.abs.mul_const _) ?_
  · have hp : Continuous (fun z : ℂ => ((r, z) : ℝ × ℂ)) := continuous_const.prodMk continuous_id
    exact h.meas.aestronglyMeasurable.mul ((continuous_hFun hW h.pos).comp hp).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_hFun_le hW h.pos r z) (abs_nonneg _)
  · refine Eventually.of_forall fun z => ?_
    exact continuous_const.mul (continuous_hFun_time hW h.pos z)

lemma intervalIntegrable_aW_sq (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ}
    (hs : 0 ≤ s) : IntervalIntegrable (fun r => aW σ W r ^ 2) volume 0 s := by
  apply ContinuousOn.intervalIntegrable
  refine ((continuous_aF h hW).pow 2).continuousOn.congr fun r hr => ?_
  rw [uIcc_of_le hs] at hr
  rw [aW_eq_integral_hFun h hr.1]; rfl

lemma Es_sub_nonpos (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : Es σ W s - Es σ W 0 ≤ 0 := by
  rw [energy_identity h hW hs hs1]
  have := intervalIntegral.integral_nonneg (μ := volume) hs (fun r _ => sq_nonneg (aW σ W r))
  linarith

theorem abs_Es_sub_le (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) : |Es σ W s - Es σ W 0| ≤ 4 * s * (N1 σ / δ) ^ 2 := by
  rw [energy_identity h hW hs hs1]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
    (f := fun r => aW σ W r ^ 2) (C := (N1 σ / δ) ^ 2) (fun r hr => by
      rw [uIoc_of_le hs] at hr
      have := abs_aW_le h hW hr.1.le (r := r)
      rw [Real.norm_eq_abs, abs_pow]
      have h0 : 0 ≤ |aW σ W r| := abs_nonneg _
      calc |aW σ W r| ^ 2 ≤ (1 / δ * N1 σ) ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = (N1 σ / δ) ^ 2 := by ring)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs] at hb
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  nlinarith

theorem abs_Es_sub_add_le (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |Es σ W s - Es σ W 0 + 4 * s * a0 σ ^ 2| ≤
      8 * N1 σ ^ 2 / δ ^ 3 * ((∫ r in (0 : ℝ)..s, |W r|) + s ^ 2 / δ) := by
  have hδ := h.pos
  have hN := N1_nonneg σ
  have hdiff : ∀ r, 0 ≤ r → |aW σ W r - a0 σ| ≤ (|W r| + 2 * r / δ) / δ ^ 2 * N1 σ := by
    intro r hr
    have i1 : Integrable (fun z => σ z * hFun W δ r z) :=
      h.integrable_mul ((continuous_hFun hW hδ).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable (by positivity)
        (fun z _ _ => abs_hFun_le hW hδ r z)
    have i2 : Integrable (fun z => σ z * (1 / z).re) :=
      h.integrable_mul measurable_one_div_re.aestronglyMeasurable (by positivity)
        (fun z hz1 _ => abs_one_div_re_le hz1 hδ)
    have e : aW σ W r - a0 σ = ∫ z, σ z * (hFun W δ r z - (1 / z).re) := by
      rw [aW_eq_integral_hFun h hr, a0, ← integral_sub i1 i2]
      congr 1; funext z; ring
    rw [e]
    refine h.abs_integral_mul_le (fun z hz1 _ => ?_)
    rw [hFun_eq hr hz1, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (TwoPointExp.norm_inv_revMap_sub_inv_le hW hδ hz1 hr)
  have hpt : ∀ r, 0 ≤ r → |aW σ W r ^ 2 - a0 σ ^ 2| ≤
      2 * N1 σ ^ 2 / δ ^ 3 * (|W r| + 2 * r / δ) := by
    intro r hr
    have h1 := hdiff r hr
    have h2 := abs_aW_le h hW hr (r := r)
    have h3 := abs_a0_le h
    have e : aW σ W r ^ 2 - a0 σ ^ 2 = (aW σ W r - a0 σ) * (aW σ W r + a0 σ) := by ring
    rw [e, abs_mul]
    have h4 : |aW σ W r + a0 σ| ≤ 2 * (1 / δ * N1 σ) := by
      linarith [abs_add_le (aW σ W r) (a0 σ)]
    calc |aW σ W r - a0 σ| * |aW σ W r + a0 σ|
        ≤ ((|W r| + 2 * r / δ) / δ ^ 2 * N1 σ) * (2 * (1 / δ * N1 σ)) :=
          mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
      _ = 2 * N1 σ ^ 2 / δ ^ 3 * (|W r| + 2 * r / δ) := by field_simp
  have hgint : IntervalIntegrable (fun r => 2 * N1 σ ^ 2 / δ ^ 3 * (|W r| + 2 * r / δ)) volume 0 s := by
    apply Continuous.intervalIntegrable; fun_prop
  have hJ := intervalIntegral.norm_integral_le_of_norm_le hs
    (f := fun r => aW σ W r ^ 2 - a0 σ ^ 2)
    (Eventually.of_forall fun r hr => (hpt r hr.1.le : _)) hgint
  have hlin : ∫ r in (0 : ℝ)..s, 2 * N1 σ ^ 2 / δ ^ 3 * (|W r| + 2 * r / δ) =
      2 * N1 σ ^ 2 / δ ^ 3 * ((∫ r in (0 : ℝ)..s, |W r|) + s ^ 2 / δ) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (hW.abs.intervalIntegrable _ _) (by apply Continuous.intervalIntegrable; fun_prop)]
    congr 2
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_id]; ring
  rw [hlin, Real.norm_eq_abs] at hJ
  have hI : ∫ r in (0 : ℝ)..s, aW σ W r ^ 2 =
      (∫ r in (0 : ℝ)..s, (aW σ W r ^ 2 - a0 σ ^ 2)) + s * a0 σ ^ 2 := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_aW_sq h hW hs) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
  rw [energy_identity h hW hs hs1, hI]
  have e : -4 * ((∫ r in (0 : ℝ)..s, (aW σ W r ^ 2 - a0 σ ^ 2)) + s * a0 σ ^ 2) +
      4 * s * a0 σ ^ 2 = -4 * ∫ r in (0 : ℝ)..s, (aW σ W r ^ 2 - a0 σ ^ 2) := by ring
  rw [e, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have : 8 * N1 σ ^ 2 / δ ^ 3 = 4 * (2 * N1 σ ^ 2 / δ ^ 3) := by ring
  rw [this, mul_assoc]
  exact mul_le_mul_of_nonneg_left hJ (by norm_num)

/-! ### The harmonic part `X_s` -/

/-- `X_s(σ) = ∫ σ(z) ((2/√κ) log ‖f_s z‖ + Qc(√κ) Re ∫_0^s 2/f_r(z)² dr) dz`. -/
def Xs (κ : ℝ) (σ : ℂ → ℝ) (W : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ z, σ z * (2 / √κ * Real.log ‖revMap W s z‖ +
    Qc (√κ) * (∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2).re)

/-- The time-zero value `X_0(σ) = ∫ σ(z) (2/√κ) log ‖z‖ dz`. -/
def X0 (κ : ℝ) (σ : ℂ → ℝ) : ℝ := ∫ z, σ z * (2 / √κ * Real.log ‖z‖)

/-- `b = ∫ σ(z) Re(1/z²) dz`. -/
def b0 (σ : ℂ → ℝ) : ℝ := ∫ z, σ z * (1 / z ^ 2).re

/-- The clamped version of `oneHFun`, measurable in `z`. -/
def oneF (κ : ℝ) (W : ℝ → ℝ) (δ s : ℝ) (z : ℂ) : ℝ :=
  2 / √κ * Real.log ‖revF W δ s z‖ + Qc (√κ) * (∫ r in (0 : ℝ)..s, 2 / revF W δ r z ^ 2).re
    - 2 / √κ * Real.log ‖z‖

lemma oneHFun_eq_oneF {κ : ℝ} {W : ℝ → ℝ} {δ s : ℝ} {z : ℂ} (hs : 0 ≤ s) (hz : δ ≤ z.im) :
    OnePointExpansion.oneHFun κ W s z = oneF κ W δ s z := by
  have hI : ∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2 = ∫ r in (0 : ℝ)..s, 2 / revF W δ r z ^ 2 := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    simp only [revF_eq hr.1 hz]
  unfold OnePointExpansion.oneHFun oneF
  rw [revF_eq hs hz, hI]

lemma continuous_timeIntegral_revF {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    Continuous (fun z => ∫ r in (0 : ℝ)..s, 2 / revF W δ r z ^ 2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact continuous_const.div (((continuous_revF hW hδ).comp continuous_swap).pow 2)
    (fun p => pow_ne_zero 2 (revF_ne_zero hW hδ p.2 p.1))

lemma measurable_oneF {κ : ℝ} {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    Measurable (oneF κ W δ s) := by
  have h1 : Continuous (fun z => revF W δ s z) :=
    (continuous_revF hW hδ).comp (continuous_const.prodMk continuous_id)
  have h2 := continuous_timeIntegral_revF hW hδ s
  refine (((measurable_const.mul (Real.measurable_log.comp h1.norm.measurable)).add
    (measurable_const.mul (Complex.measurable_re.comp h2.measurable))).sub
    (measurable_const.mul (Real.measurable_log.comp continuous_norm.measurable)))

lemma abs_log_sub_log_le {a b δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hb : δ ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / δ := by
  have ha0 : 0 < a := hδ.trans_le ha
  have hb0 : 0 < b := hδ.trans_le hb
  have k1 : Real.log a - Real.log b ≤ |a - b| / δ := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have e : a / b - 1 = (a - b) / b := by field_simp
    have k : (a - b) / b ≤ |a - b| / δ := by
      calc (a - b) / b ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
        _ ≤ |a - b| / δ := div_le_div_of_nonneg_left (abs_nonneg _) hδ hb
    linarith
  have k2 : Real.log b - Real.log a ≤ |a - b| / δ := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have e : b / a - 1 = (b - a) / a := by field_simp
    have k : (b - a) / a ≤ |a - b| / δ := by
      calc (b - a) / a ≤ |a - b| / a := by
            apply div_le_div_of_nonneg_right _ ha0.le; rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ |a - b| / δ := div_le_div_of_nonneg_left (abs_nonneg _) hδ ha
    linarith
  rw [abs_le]; constructor <;> linarith

lemma norm_timeIntegral_le {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : δ ≤ z.im) {s : ℝ} (hs : 0 ≤ s) :
    ‖∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2‖ ≤ 2 / δ ^ 2 * s := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
    (f := fun r => 2 / revMap W r z ^ 2) (C := 2 / δ ^ 2) (fun r hr => by
      rw [uIoc_of_le hs] at hr
      have hn := TwoPointExp.le_norm_revMap hW hδ hz hr.1.le
      rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hδ.le hn 2))
  rwa [sub_zero, abs_of_nonneg hs] at this

lemma Qc_pos {κ : ℝ} (hκ : 0 < κ) : 0 < Qc (√κ) := by
  have := Real.sqrt_pos.mpr hκ
  unfold Qc; positivity

/-- Crude bound `|𝔥_s(z)| ≤ 2|B_s|/δ + cX s`. -/
lemma abs_oneHFun_le {κ : ℝ} (hκ : 0 < κ) {W B : ℝ → ℝ} (hW : Continuous W)
    (hWB : ∀ r, W r = √κ * B r) {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : δ ≤ z.im) {s : ℝ}
    (hs : 0 ≤ s) :
    |OnePointExpansion.oneHFun κ W s z| ≤
      2 / δ * |B s| + (4 / (√κ * δ ^ 2) + 2 * Qc (√κ) / δ ^ 2) * s := by
  have hγ : 0 < √κ := Real.sqrt_pos.mpr hκ
  have hQ := Qc_pos hκ
  have hzn : δ ≤ ‖z‖ := hz.trans (Complex.im_le_norm z)
  have hfn := TwoPointExp.le_norm_revMap hW hδ hz hs
  have hlog := abs_log_sub_log_le hδ hfn hzn
  have hdisp := OnePointExpansion.norm_revMap_sub_self_le W hW hδ hz hs
  have hnn : |‖revMap W s z‖ - ‖z‖| ≤ ‖revMap W s z - z‖ := abs_norm_sub_norm_le _ _
  have hL := norm_timeIntegral_le hW hδ hz hs
  have hLre := (Complex.abs_re_le_norm (∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2)).trans hL
  rw [hWB s, abs_mul, abs_of_pos hγ] at hdisp
  unfold OnePointExpansion.oneHFun
  have e : 2 / √κ * Real.log ‖revMap W s z‖ +
      Qc (√κ) * (∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2).re - 2 / √κ * Real.log ‖z‖ =
      2 / √κ * (Real.log ‖revMap W s z‖ - Real.log ‖z‖) +
        Qc (√κ) * (∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2).re := by ring
  rw [e]
  have k1 : |2 / √κ * (Real.log ‖revMap W s z‖ - Real.log ‖z‖)| ≤
      2 / √κ * ((√κ * |B s| + 2 * s / δ) / δ) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / √κ)]
    refine mul_le_mul_of_nonneg_left (hlog.trans ?_) (by positivity)
    exact div_le_div_of_nonneg_right (hnn.trans hdisp) hδ.le
  have k2 : |Qc (√κ) * (∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2).re| ≤
      Qc (√κ) * (2 / δ ^ 2 * s) := by
    rw [abs_mul, abs_of_pos hQ]; exact mul_le_mul_of_nonneg_left hLre hQ.le
  have k3 : 2 / √κ * ((√κ * |B s| + 2 * s / δ) / δ) + Qc (√κ) * (2 / δ ^ 2 * s) =
      2 / δ * |B s| + (4 / (√κ * δ ^ 2) + 2 * Qc (√κ) / δ ^ 2) * s := by
    field_simp; ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add k1 k2
    _ = _ := k3

lemma integrable_oneHFun (h : IsGenTest σ δ R M) {κ : ℝ} (hκ : 0 < κ) {W B : ℝ → ℝ}
    (hW : Continuous W) (hWB : ∀ r, W r = √κ * B r) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun z => σ z * OnePointExpansion.oneHFun κ W s z) := by
  rw [h.mul_congr (g' := oneF κ W δ s) (fun z hz1 _ => oneHFun_eq_oneF hs hz1)]
  have hQ := Qc_pos hκ
  refine h.integrable_mul (measurable_oneF hW h.pos s).aestronglyMeasurable
    (C := 2 / δ * |B s| + (4 / (√κ * δ ^ 2) + 2 * Qc (√κ) / δ ^ 2) * s)
    (by have := h.pos; positivity) (fun z hz1 _ => ?_)
  rw [← oneHFun_eq_oneF hs hz1]
  exact abs_oneHFun_le hκ hW hWB h.pos hz1 hs

lemma integrable_X0_integrand (h : IsGenTest σ δ R M) (κ : ℝ) :
    Integrable (fun z => σ z * (2 / √κ * Real.log ‖z‖)) := by
  refine h.integrable_mul ((measurable_const.mul
    (Real.measurable_log.comp continuous_norm.measurable))).aestronglyMeasurable
    (C := |2 / √κ| * (|Real.log δ| + |Real.log R|)) (by positivity) (fun z hz1 hz2 => ?_)
  have hzn : δ ≤ ‖z‖ := hz1.trans (Complex.im_le_norm z)
  have l1 := Real.log_le_log h.pos hzn
  have l2 := Real.log_le_log (h.pos.trans_le hzn) hz2
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_le]; constructor <;>
    linarith [neg_abs_le (Real.log δ), le_abs_self (Real.log R), abs_nonneg (Real.log δ),
      abs_nonneg (Real.log R)]

lemma Xs_sub_X0 (h : IsGenTest σ δ R M) {κ : ℝ} (hκ : 0 < κ) {W B : ℝ → ℝ}
    (hW : Continuous W) (hWB : ∀ r, W r = √κ * B r) {s : ℝ} (hs : 0 ≤ s) :
    Xs κ σ W s - X0 κ σ = ∫ z, σ z * OnePointExpansion.oneHFun κ W s z := by
  have e : Xs κ σ W s = ∫ z, (σ z * OnePointExpansion.oneHFun κ W s z +
      σ z * (2 / √κ * Real.log ‖z‖)) := by
    unfold Xs; congr 1; funext z; unfold OnePointExpansion.oneHFun; ring
  rw [e, integral_add (integrable_oneHFun h hκ hW hWB hs) (integrable_X0_integrand h κ), X0]
  ring

lemma abs_Xs_sub_X0_le (h : IsGenTest σ δ R M) {κ : ℝ} (hκ : 0 < κ) {W B : ℝ → ℝ}
    (hW : Continuous W) (hWB : ∀ r, W r = √κ * B r) {s : ℝ} (hs : 0 ≤ s) :
    |Xs κ σ W s - X0 κ σ| ≤
      (2 / δ * |B s| + (4 / (√κ * δ ^ 2) + 2 * Qc (√κ) / δ ^ 2) * s) * N1 σ := by
  rw [Xs_sub_X0 h hκ hW hWB hs]
  exact h.abs_integral_mul_le (fun z hz1 _ => abs_oneHFun_le hκ hW hWB h.pos hz1 hs)

/-- The second-order expansion of `X_s - X_0`, integrated against `σ`. -/
theorem abs_Xs_sub_X0_sub_expansion_le (h : IsGenTest σ δ R M) {κ : ℝ} (hκ : 0 < κ)
    {W B : ℝ → ℝ} (hW : Continuous W) (hWB : ∀ r, W r = √κ * B r) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s ≤ 1) :
    |Xs κ σ W s - X0 κ σ - (-2 * a0 σ * B s - √κ * b0 σ * (B s ^ 2 - s))| ≤
      OnePointExpansion.C₄ κ δ R * (|B s| ^ 3 + s * |B s| + (∫ r in (0 : ℝ)..s, |W r|) + s ^ 2)
        * N1 σ := by
  have hδ := h.pos
  have i1 : Integrable (fun z => σ z * (1 / z).re) :=
    h.integrable_mul measurable_one_div_re.aestronglyMeasurable (by positivity)
      (fun z hz1 _ => abs_one_div_re_le hz1 hδ)
  have i2 : Integrable (fun z => σ z * (1 / z ^ 2).re) := by
    refine h.integrable_mul measurable_one_div_sq_re.aestronglyMeasurable (C := 1 / δ ^ 2)
      (by positivity) (fun z hz1 _ => ?_)
    have hzn : δ ≤ ‖z‖ := hz1.trans (Complex.im_le_norm z)
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_one, norm_pow]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (pow_le_pow_left₀ hδ.le hzn 2)
  have elin : -2 * a0 σ * B s - √κ * b0 σ * (B s ^ 2 - s) =
      ∫ z, σ z * (-2 * (1 / z).re * B s - √κ * (1 / z ^ 2).re * (B s ^ 2 - s)) := by
    have e : (fun z => σ z * (-2 * (1 / z).re * B s - √κ * (1 / z ^ 2).re * (B s ^ 2 - s))) =
        fun z => (-2 * B s) * (σ z * (1 / z).re) - (√κ * (B s ^ 2 - s)) * (σ z * (1 / z ^ 2).re) := by
      funext z; ring
    rw [e, integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
      a0, b0]; ring
  have ilin : Integrable (fun z => σ z * (-2 * (1 / z).re * B s - √κ * (1 / z ^ 2).re * (B s ^ 2 - s))) := by
    have e : (fun z => σ z * (-2 * (1 / z).re * B s - √κ * (1 / z ^ 2).re * (B s ^ 2 - s))) =
        fun z => (-2 * B s) * (σ z * (1 / z).re) - (√κ * (B s ^ 2 - s)) * (σ z * (1 / z ^ 2).re) := by
      funext z; ring
    rw [e]; exact (i1.const_mul _).sub (i2.const_mul _)
  rw [Xs_sub_X0 h hκ hW hWB hs, elin, ← integral_sub (integrable_oneHFun h hκ hW hWB hs) ilin]
  have e2 : (fun z => σ z * OnePointExpansion.oneHFun κ W s z -
      σ z * (-2 * (1 / z).re * B s - √κ * (1 / z ^ 2).re * (B s ^ 2 - s))) =
      fun z => σ z * (OnePointExpansion.oneHFun κ W s z -
        (-2 * (1 / z).re * B s - √κ * (1 / z ^ 2).re * (B s ^ 2 - s))) := by
    funext z; ring
  rw [e2]
  exact h.abs_integral_mul_le (fun z hz1 hz2 =>
    OnePointExpansion.oneHFun_expansion hκ hW hWB hδ hz1 hz2 hs hs1)

/-! ### Measurability in the Brownian path -/

/-- The clamped integrand of `Xs`, continuous in `z`. -/
def AF (κ : ℝ) (W : ℝ → ℝ) (δ s : ℝ) (z : ℂ) : ℝ :=
  2 / √κ * Real.log ‖revF W δ s z‖ + Qc (√κ) * (∫ r in (0 : ℝ)..s, 2 / revF W δ r z ^ 2).re

lemma continuous_revF_space {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    Continuous (fun z : ℂ => revF W δ r z) := by
  have hp : Continuous (fun z : ℂ => ((r, z) : ℝ × ℂ)) := continuous_const.prodMk continuous_id
  exact (continuous_revF hW hδ).comp hp

lemma continuous_hFun_space {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    Continuous (fun z : ℂ => hFun W δ r z) :=
  Complex.continuous_re.comp (continuous_const.div (continuous_revF_space hW hδ r)
    (fun z => revF_ne_zero hW hδ r z))

lemma continuous_AF {κ : ℝ} {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    Continuous (AF κ W δ s) :=
  (continuous_const.mul ((continuous_revF_space hW hδ s).norm.log
    (fun z => norm_ne_zero_iff.mpr (revF_ne_zero hW hδ s z)))).add
    (continuous_const.mul (Complex.continuous_re.comp (continuous_timeIntegral_revF hW hδ s)))

lemma timeIntegral_revF_eq {W : ℝ → ℝ} {δ s : ℝ} {z : ℂ} (hs : 0 ≤ s) (hz : δ ≤ z.im) :
    ∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2 = ∫ r in (0 : ℝ)..s, 2 / revF W δ r z ^ 2 := by
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs] at hr
  simp only [revF_eq hr.1 hz]

lemma Xs_eq_AF (h : IsGenTest σ δ R M) {κ : ℝ} {W : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    Xs κ σ W s = ∫ z, σ z * AF κ W δ s z := by
  unfold Xs
  rw [h.mul_congr (g' := AF κ W δ s) (fun z hz1 _ => by
    rw [AF, revF_eq hs hz1, timeIntegral_revF_eq hs hz1])]

section Path

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
lemma continuous_drive (κ : ℝ) (hc : ∀ ω, Continuous fun t => B t ω) (ω : Ω) :
    Continuous (drive κ B ω) :=
  continuous_const.mul ((hc ω).comp continuous_real_toNNReal)

lemma measurable_revF_drive (κ : ℝ) (hB : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) (z : ℂ) :
    Measurable fun ω => revF (drive κ B ω) δ r z :=
  ReverseFlow.measurable_revMap_drive κ B hB hc (clampH δ z) (hδ.trans_le (clampH_im_ge δ z))
    (le_max_right r 0)

lemma measurable_timeIntegral_drive (κ : ℝ) (hB : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : 0 ≤ s) (z : ℂ) :
    Measurable fun ω => ∫ r in (0 : ℝ)..s, 2 / revF (drive κ B ω) δ r z ^ 2 := by
  have hj : Measurable (Function.uncurry fun (r : ℝ) (ω : Ω) =>
      2 / revF (drive κ B ω) δ r z ^ 2) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => continuous_const.div ((continuous_revF_time (continuous_drive κ hc ω) hδ z).pow 2)
        (fun r => pow_ne_zero 2 (revF_ne_zero (continuous_drive κ hc ω) hδ r z)))
      (fun r => measurable_const.div ((measurable_revF_drive κ hB hc hδ r z).pow_const 2))
  simp_rw [intervalIntegral.integral_of_le hs]
  exact (hj.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc (0 : ℝ) s))).measurable

lemma measurable_Xs_drive (h : IsGenTest σ δ R M) (κ : ℝ) (hB : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) {s : ℝ} (hs : 0 ≤ s) :
    Measurable fun ω => Xs κ σ (drive κ B ω) s := by
  have hj : Measurable (Function.uncurry fun (z : ℂ) (ω : Ω) => AF κ (drive κ B ω) δ s z) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => continuous_AF (continuous_drive κ hc ω) h.pos s)
      (fun z => (measurable_const.mul (Real.measurable_log.comp
        (measurable_revF_drive κ hB hc h.pos s z).norm)).add
        (measurable_const.mul (Complex.measurable_re.comp
          (measurable_timeIntegral_drive κ hB hc h.pos hs z))))
  have hj2 : Measurable (Function.uncurry fun (z : ℂ) (ω : Ω) => σ z * AF κ (drive κ B ω) δ s z) :=
    (h.meas.comp measurable_fst).mul hj
  have := (hj2.stronglyMeasurable.integral_prod_left (μ := (volume : Measure ℂ))).measurable
  have e : (fun ω => Xs κ σ (drive κ B ω) s) = fun ω => ∫ z, σ z * AF κ (drive κ B ω) δ s z := by
    funext ω; exact Xs_eq_AF h hs
  rw [e]; exact this

lemma measurable_aF_drive (h : IsGenTest σ δ R M) (κ : ℝ) (hB : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) :
    Measurable (Function.uncurry fun (r : ℝ) (ω : Ω) => ∫ z, σ z * hFun (drive κ B ω) δ r z) := by
  refine measurable_uncurry_of_continuous_of_measurable
    (fun ω => continuous_aF h (continuous_drive κ hc ω)) (fun r => ?_)
  have hj : Measurable (Function.uncurry fun (z : ℂ) (ω : Ω) => σ z * hFun (drive κ B ω) δ r z) :=
    (h.meas.comp measurable_fst).mul (measurable_uncurry_of_continuous_of_measurable
      (fun ω => continuous_hFun_space (continuous_drive κ hc ω) h.pos r)
      (fun z => Complex.measurable_re.comp
        (measurable_const.div (measurable_revF_drive κ hB hc h.pos r z))))
  exact (hj.stronglyMeasurable.integral_prod_left (μ := (volume : Measure ℂ))).measurable

lemma Es_eq_E0_sub (h : IsGenTest σ δ R M) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s ≤ 1) :
    Es σ W s = E0 σ - 4 * ∫ r in (0 : ℝ)..s, (∫ z, σ z * hFun W δ r z) ^ 2 := by
  have e := energy_identity h hW hs hs1
  rw [Es_zero h hW] at e
  have e2 : ∫ r in (0 : ℝ)..s, (∫ z, σ z * hFun W δ r z) ^ 2 =
      ∫ r in (0 : ℝ)..s, aW σ W r ^ 2 := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    simp only [aW_eq_integral_hFun h hr.1]
  rw [e2]; linarith

lemma measurable_Es_drive (h : IsGenTest σ δ R M) (κ : ℝ) (hB : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Measurable fun ω => Es σ (drive κ B ω) s := by
  have e : (fun ω => Es σ (drive κ B ω) s) = fun ω =>
      E0 σ - 4 * ∫ r in (0 : ℝ)..s, (∫ z, σ z * hFun (drive κ B ω) δ r z) ^ 2 := by
    funext ω; exact Es_eq_E0_sub h (continuous_drive κ hc ω) hs hs1
  rw [e]
  have hj : Measurable (Function.uncurry fun (r : ℝ) (ω : Ω) =>
      (∫ z, σ z * hFun (drive κ B ω) δ r z) ^ 2) := (measurable_aF_drive h κ hB hc).pow_const 2
  simp_rw [intervalIntegral.integral_of_le hs]
  exact measurable_const.sub (measurable_const.mul
    (hj.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc (0 : ℝ) s))).measurable)

variable {P : Measure Ω}

lemma integrable_timeIntegral_abs_pow (hB : IsPreBrownianReal B P) (hmeas : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..s, |B r.toNNReal ω| ^ n) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hj0 : Measurable (Function.uncurry fun (r : ℝ) (ω : Ω) => |B r.toNNReal ω| ^ n) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => ((hc ω).comp continuous_real_toNNReal).abs.pow n)
      (fun r => (continuous_abs.measurable.comp (hmeas r.toNNReal)).pow_const n)
  have hj : Measurable (fun p : Ω × ℝ => |B p.2.toNNReal p.1| ^ n) := hj0.comp measurable_swap
  have hIfin : (volume : Measure ℝ) (Ioc 0 s) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hint : Integrable (fun p : Ω × ℝ => |B p.2.toNNReal p.1| ^ n)
      (P.prod (volume.restrict (Ioc 0 s))) := by
    rw [integrable_prod_iff' hj.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun r => integrable_pow hB r.toNNReal n, ?_⟩
    have hm2 : AEStronglyMeasurable (fun r : ℝ => ∫ ω, ‖|B r.toNNReal ω| ^ n‖ ∂P)
        (volume.restrict (Ioc 0 s)) :=
      (hj.norm.stronglyMeasurable.integral_prod_left' (μ := P)).aestronglyMeasurable
    refine Integrable.mono' (g := fun _ => gaussianAbsMoment n * s ^ ((n : ℝ) / 2))
      (integrableOn_const hIfin) hm2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have e : (fun ω => ‖|B r.toNNReal ω| ^ n‖) = fun ω => |B r.toNNReal ω| ^ n := by
      funext ω; rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    rw [e, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _)]
    have h1 := integral_abs_pow_le hB r.toNNReal n
    rw [Real.coe_toNNReal r hr.1.le] at h1
    refine h1.trans ?_
    gcongr
    exacts [gaussianAbsMoment_nonneg n, hr.1.le, hr.2]
  have := hint.integral_prod_left
  simp_rw [intervalIntegral.integral_of_le hs]
  exact this

end Path

/-! ### Deterministic Taylor bound -/

/-- Second-order Taylor remainder of `exp` with a cubic bound valid for all `w`. -/
lemma norm_exp_sub_taylor2_le (w : ℂ) :
    ‖Complex.exp w - 1 - w - w ^ 2 / 2‖ ≤ (Real.exp |w.re| + 3) * ‖w‖ ^ 3 := by
  have hE : 1 ≤ Real.exp |w.re| := Real.one_le_exp (abs_nonneg _)
  by_cases hw : ‖w‖ ≤ 1
  · have hb := Complex.exp_bound hw (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, w ^ m / (m.factorial : ℂ) = 1 + w + w ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at hb
    have e : Complex.exp w - 1 - w - w ^ 2 / 2 = Complex.exp w - (1 + w + w ^ 2 / 2) := by ring
    rw [e]
    refine hb.trans ?_
    have hc : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹ ≤ 1 := by
      norm_num [Nat.factorial]
    have h3 : 0 ≤ ‖w‖ ^ 3 := by positivity
    calc ‖w‖ ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹)
        ≤ ‖w‖ ^ 3 * 1 := mul_le_mul_of_nonneg_left hc h3
      _ ≤ (Real.exp |w.re| + 3) * ‖w‖ ^ 3 := by nlinarith
  · push Not at hw
    have hexp : ‖Complex.exp w‖ ≤ Real.exp |w.re| := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (le_abs_self _)
    have h1 : ‖Complex.exp w - 1 - w - w ^ 2 / 2‖ ≤
        ‖Complex.exp w‖ + 1 + ‖w‖ + ‖w‖ ^ 2 / 2 := by
      have := norm_sub_le (Complex.exp w - 1 - w) (w ^ 2 / 2)
      have := norm_sub_le (Complex.exp w - 1) w
      have := norm_sub_le (Complex.exp w) 1
      rw [norm_div, norm_pow, norm_one] at *
      simp only [Complex.norm_ofNat] at *
      linarith
    have hw2 : ‖w‖ ≤ ‖w‖ ^ 2 := by nlinarith
    have hw3 : ‖w‖ ^ 2 ≤ ‖w‖ ^ 3 := by nlinarith
    have hw1 : 1 ≤ ‖w‖ ^ 3 := by nlinarith
    nlinarith

/-- The explicit pointwise constant. -/
def Kall (N δ γ C4 cs : ℝ) : ℝ :=
  4 * (Real.exp (2 * (N / δ) ^ 2) + 3) * (2 * (N / δ) ^ 2 + (2 / δ + cs) * N) ^ 3
    + 4 * N ^ 2 / δ ^ 3 * (1 + 1 / δ) + 2 * (N / δ) ^ 4
    + (2 * (C4 * N) + γ * N / δ ^ 2) * ((2 / δ + cs) * N + 2 * N / δ) / 2
    + C4 * N + 2 * (N / δ) ^ 2 * ((2 / δ + cs) * N)

/-- Polynomial facts used in `pointwise_key` (`q = √s`). -/
lemma poly_facts {β s q m V : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hqs : q ^ 2 = s) (hm : 0 ≤ m) (hV : 0 ≤ V)
    (hmβ : m * β ≤ (V + s * β ^ 2) / 2) :
    0 ≤ β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q ∧
    β ^ 3 + s * β + m + s ^ 2 ≤ β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q ∧
    (β ^ 3 + s * β + m + s ^ 2) * (β + s) ≤
      2 * (β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q) ∧
    (β ^ 2 + s) * (β + s) ≤ β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q ∧
    s * (β + s) ≤ β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q ∧
    (β + s) ^ 3 ≤ 4 * (β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q) ∧
    s ^ 2 ≤ β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q ∧
    m ≤ β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q := by
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have F1 : s ^ 2 ≤ s * q := by
    calc s ^ 2 = s * q ^ 2 := by rw [hqs]; ring
      _ ≤ s * q := mul_le_mul_of_nonneg_left hq2 hs
  have hs2 : s ^ 2 ≤ s := by nlinarith
  have hs3 : s ^ 3 ≤ s ^ 2 := by nlinarith
  have hsq : 0 ≤ s * q := mul_nonneg hs hq0
  have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
  have hβ3 : 0 ≤ β ^ 3 := pow_nonneg hβ 3
  have hβ4 : 0 ≤ β ^ 4 := pow_nonneg hβ 4
  have hsβ : 0 ≤ s * β := mul_nonneg hs hβ
  have hsβ2 : 0 ≤ s * β ^ 2 := mul_nonneg hs hβ2
  have k1 : s * β ^ 3 ≤ β ^ 3 := mul_le_of_le_one_left hβ3 hs1
  have k2 : s ^ 2 * β ≤ s * β := mul_le_mul_of_nonneg_right hs2 hβ
  have k3 : m * s ≤ m := mul_le_of_le_one_right hm hs1
  have k4 : s ^ 2 * β ^ 2 ≤ s * β ^ 2 := mul_le_mul_of_nonneg_right hs2 hβ2
  have k5 : β ^ 2 * s ≤ β ^ 2 := mul_le_of_le_one_right hβ2 hs1
  refine ⟨by positivity, by linarith, ?_, ?_, ?_, ?_, by linarith, by linarith⟩
  · have e : (β ^ 3 + s * β + m + s ^ 2) * (β + s) =
        β ^ 4 + s * β ^ 3 + s * β ^ 2 + s ^ 2 * β + m * β + m * s + s ^ 2 * β + s ^ 3 := by ring
    rw [e]; linarith
  · have e : (β ^ 2 + s) * (β + s) = β ^ 3 + s * β ^ 2 + s * β + s ^ 2 := by ring
    rw [e]; linarith
  · have e : s * (β + s) = s * β + s ^ 2 := by ring
    rw [e]; linarith
  · have h4 : (β + s) ^ 3 ≤ 4 * (β ^ 3 + s ^ 3) := by
      have e : 4 * (β ^ 3 + s ^ 3) - (β + s) ^ 3 = 3 * (β + s) * (β - s) ^ 2 := by ring
      have : 0 ≤ 3 * (β + s) * (β - s) ^ 2 := by positivity
      linarith
    linarith

/-- **Pointwise second-order bound.** All the random quantities enter only through real
numbers; the cancellations happen in expectation. -/
lemma pointwise_key {N δ γ C4 cs a bb s b m V X e : ℝ} (hN : 0 ≤ N) (hδ : 0 < δ) (hγ : 0 < γ)
    (hC4 : 0 ≤ C4) (hcs : 0 ≤ cs) (ha : |a| ≤ N / δ) (hbb : |bb| ≤ N / δ ^ 2) (hs : 0 ≤ s)
    (hs1 : s ≤ 1) (hm : 0 ≤ m) (hV : 0 ≤ V) (hmβ : m * |b| ≤ (V + s * |b| ^ 2) / 2)
    (hX : |X| ≤ (2 / δ * |b| + cs * s) * N)
    (hRX : |X - (-2 * a * b - γ * bb * (b ^ 2 - s))| ≤ C4 * (|b| ^ 3 + s * |b| + m + s ^ 2) * N)
    (he0 : 0 ≤ e) (he1 : e ≤ 2 * s * (N / δ) ^ 2)
    (hRE : |e - 2 * s * a ^ 2| ≤ 4 * N ^ 2 / δ ^ 3 * (m + s ^ 2 / δ)) :
    ‖Complex.exp (e + I * X) - 1 -
        (((2 * a ^ 2 * (s - b ^ 2) : ℝ) : ℂ) + I * ((-2 * a * b - γ * bb * (b ^ 2 - s) : ℝ) : ℂ))‖
      ≤ Kall N δ γ C4 cs * (|b| ^ 3 + |b| ^ 4 + s * |b| + s * |b| ^ 2 + m + V + s * √s) := by
  have hβ : 0 ≤ |b| := abs_nonneg b
  have hb2 : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  have hab : |2 * a * b| ≤ 2 * (N / δ) * |b| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num)) hβ
  have hq0 : 0 ≤ √s := Real.sqrt_nonneg s
  have hq1 : √s ≤ 1 := Real.sqrt_le_one.mpr hs1
  have hqs : √s ^ 2 = s := Real.sq_sqrt hs
  have hbs : |b ^ 2 - s| ≤ |b| ^ 2 + s := by
    rw [hb2, abs_le]; constructor <;> nlinarith [sq_nonneg |b|]
  generalize hβdef : |b| = β at hβ hmβ hX hRX hb2 hab hbs ⊢
  generalize hqdef : √s = q at hq0 hq1 hqs ⊢
  obtain ⟨PD0, F2, F3, F4, F5, F6, F8, F9⟩ := poly_facts hβ hs hs1 hq0 hq1 hqs hm hV hmβ
  generalize hD : β ^ 3 + β ^ 4 + s * β + s * β ^ 2 + m + V + s * q = D at PD0 F2 F3 F4 F5 F6 F8 F9 ⊢
  generalize hA : (2 / δ + cs) * N = A
  generalize hNd : N / δ = Nd at ha hbb he1 hab
  have hNd0 : 0 ≤ Nd := hNd ▸ div_nonneg hN hδ.le
  have hA0 : 0 ≤ A := hA ▸ mul_nonneg (by positivity) hN
  have hCr0 : 0 ≤ C4 * N := mul_nonneg hC4 hN
  have hKb0 : 0 ≤ γ * N / δ ^ 2 := div_nonneg (mul_nonneg hγ.le hN) (by positivity)
  have hu0 : 0 ≤ β + s := add_nonneg hβ hs
  -- the bound on X
  have hXu : |X| ≤ A * (β + s) := by
    rw [← hA]
    have h1 : 2 / δ * β + cs * s ≤ (2 / δ + cs) * (β + s) := by
      have : 0 ≤ 2 / δ * s := by positivity
      have : 0 ≤ cs * β := mul_nonneg hcs hβ
      have e : (2 / δ + cs) * (β + s) = 2 / δ * β + cs * s + (2 / δ * s + cs * β) := by ring
      linarith
    calc |X| ≤ (2 / δ * β + cs * s) * N := hX
      _ ≤ (2 / δ + cs) * (β + s) * N := mul_le_mul_of_nonneg_right h1 hN
      _ = (2 / δ + cs) * N * (β + s) := by ring
  -- the Taylor part
  generalize hw : (e : ℂ) + I * (X : ℂ) = w
  have hwre : w.re = e := by rw [← hw]; simp
  have hwn : ‖w‖ ≤ (2 * Nd ^ 2 + A) * (β + s) := by
    have h1 : ‖w‖ ≤ e + |X| := by
      rw [← hw]
      calc ‖(e : ℂ) + I * (X : ℂ)‖ ≤ ‖(e : ℂ)‖ + ‖I * (X : ℂ)‖ := norm_add_le _ _
        _ = e + |X| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg he0]
    have h2 : e ≤ 2 * Nd ^ 2 * (β + s) := by
      have : 2 * s * Nd ^ 2 ≤ 2 * Nd ^ 2 * (β + s) := by
        have : 0 ≤ 2 * Nd ^ 2 * β := by positivity
        have e : 2 * Nd ^ 2 * (β + s) = 2 * s * Nd ^ 2 + 2 * Nd ^ 2 * β := by ring
        linarith
      linarith
    have e : (2 * Nd ^ 2 + A) * (β + s) = 2 * Nd ^ 2 * (β + s) + A * (β + s) := by ring
    linarith
  have hA10 : 0 ≤ 2 * Nd ^ 2 + A := by positivity
  have hw3 : ‖w‖ ^ 3 ≤ 4 * (2 * Nd ^ 2 + A) ^ 3 * D := by
    have := pow_le_pow_left₀ (norm_nonneg w) hwn 3
    calc ‖w‖ ^ 3 ≤ ((2 * Nd ^ 2 + A) * (β + s)) ^ 3 := this
      _ = (2 * Nd ^ 2 + A) ^ 3 * (β + s) ^ 3 := by ring
      _ ≤ (2 * Nd ^ 2 + A) ^ 3 * (4 * D) := mul_le_mul_of_nonneg_left F6 (pow_nonneg hA10 3)
      _ = 4 * (2 * Nd ^ 2 + A) ^ 3 * D := by ring
  have hexp : Real.exp |w.re| ≤ Real.exp (2 * Nd ^ 2) := by
    rw [hwre, abs_of_nonneg he0]
    apply Real.exp_le_exp.mpr
    have : 2 * s * Nd ^ 2 ≤ 2 * Nd ^ 2 := by
      have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ 2 * Nd ^ 2)
      linarith
    linarith
  have hT : ‖Complex.exp w - 1 - w - w ^ 2 / 2‖ ≤
      4 * (Real.exp (2 * Nd ^ 2) + 3) * (2 * Nd ^ 2 + A) ^ 3 * D := by
    refine (norm_exp_sub_taylor2_le w).trans ?_
    calc (Real.exp |w.re| + 3) * ‖w‖ ^ 3
        ≤ (Real.exp (2 * Nd ^ 2) + 3) * (4 * (2 * Nd ^ 2 + A) ^ 3 * D) :=
          mul_le_mul (by linarith) hw3 (by positivity) (by positivity)
      _ = _ := by ring
  -- the algebraic identity
  have hid : Complex.exp w - 1 -
      (((2 * a ^ 2 * (s - b ^ 2) : ℝ) : ℂ) + I * ((-2 * a * b - γ * bb * (b ^ 2 - s) : ℝ) : ℂ)) =
      (Complex.exp w - 1 - w - w ^ 2 / 2) +
        ((((e - 2 * s * a ^ 2) + e ^ 2 / 2 - (X + 2 * a * b) * (X - 2 * a * b) / 2 : ℝ) : ℂ) +
          I * (((X - (-2 * a * b - γ * bb * (b ^ 2 - s))) + e * X : ℝ) : ℂ)) := by
    rw [← hw]
    push_cast
    linear_combination ((X : ℂ) ^ 2 / 2) * Complex.I_sq
  rw [hid]
  generalize hRXd : X - (-2 * a * b - γ * bb * (b ^ 2 - s)) = RX at hRX
  have hsplit : ∀ x y : ℝ, ‖(x : ℂ) + I * (y : ℂ)‖ ≤ |x| + |y| := fun x y => by
    calc ‖(x : ℂ) + I * (y : ℂ)‖ ≤ ‖(x : ℂ)‖ + ‖I * (y : ℂ)‖ := norm_add_le _ _
      _ = |x| + |y| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  -- real part
  have hRX' : |RX| ≤ C4 * N * (β ^ 3 + s * β + m + s ^ 2) := by
    have e : C4 * (β ^ 3 + s * β + m + s ^ 2) * N = C4 * N * (β ^ 3 + s * β + m + s ^ 2) := by
      ring
    linarith
  have hplus : |X + 2 * a * b| ≤ C4 * N * (β ^ 3 + s * β + m + s ^ 2) +
      γ * N / δ ^ 2 * (β ^ 2 + s) := by
    have e1 : X + 2 * a * b = RX - γ * bb * (b ^ 2 - s) := by rw [← hRXd]; ring
    have e2 : |γ * bb * (b ^ 2 - s)| ≤ γ * N / δ ^ 2 * (β ^ 2 + s) := by
      rw [abs_mul, abs_mul, abs_of_pos hγ]
      have hbb' : |bb| ≤ N / δ ^ 2 := hbb
      calc γ * |bb| * |b ^ 2 - s| ≤ γ * (N / δ ^ 2) * (β ^ 2 + s) := by gcongr
        _ = γ * N / δ ^ 2 * (β ^ 2 + s) := by ring
    rw [e1]
    calc |RX - γ * bb * (b ^ 2 - s)| ≤ |RX| + |γ * bb * (b ^ 2 - s)| := abs_sub _ _
      _ ≤ _ := add_le_add hRX' e2
  have hminus : |X - 2 * a * b| ≤ (A + 2 * Nd) * (β + s) := by
    have h2 : 2 * Nd * β ≤ 2 * Nd * (β + s) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc |X - 2 * a * b| ≤ |X| + |2 * a * b| := abs_sub _ _
      _ ≤ A * (β + s) + 2 * Nd * (β + s) := by linarith
      _ = (A + 2 * Nd) * (β + s) := by ring
  have hprod : |(X + 2 * a * b) * (X - 2 * a * b)| ≤
      (A + 2 * Nd) * (2 * (C4 * N) + γ * N / δ ^ 2) * D := by
    rw [abs_mul]
    have hP0 : 0 ≤ C4 * N * (β ^ 3 + s * β + m + s ^ 2) + γ * N / δ ^ 2 * (β ^ 2 + s) :=
      (abs_nonneg _).trans hplus
    calc |X + 2 * a * b| * |X - 2 * a * b|
        ≤ (C4 * N * (β ^ 3 + s * β + m + s ^ 2) + γ * N / δ ^ 2 * (β ^ 2 + s)) *
            ((A + 2 * Nd) * (β + s)) := mul_le_mul hplus hminus (abs_nonneg _) hP0
      _ = (A + 2 * Nd) * (C4 * N * ((β ^ 3 + s * β + m + s ^ 2) * (β + s)) +
            γ * N / δ ^ 2 * ((β ^ 2 + s) * (β + s))) := by ring
      _ ≤ (A + 2 * Nd) * (C4 * N * (2 * D) + γ * N / δ ^ 2 * D) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add (mul_le_mul_of_nonneg_left F3 hCr0) (mul_le_mul_of_nonneg_left F4 hKb0)
      _ = (A + 2 * Nd) * (2 * (C4 * N) + γ * N / δ ^ 2) * D := by ring
  have hRE' : |e - 2 * s * a ^ 2| ≤ 4 * N ^ 2 / δ ^ 3 * (1 + 1 / δ) * D := by
    refine hRE.trans ?_
    have F7 : m + s ^ 2 / δ ≤ (1 + 1 / δ) * D := by
      have : s ^ 2 / δ ≤ D / δ := div_le_div_of_nonneg_right F8 hδ.le
      have e : (1 + 1 / δ) * D = D + D / δ := by ring
      linarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left F7 (by positivity)
  have he2 : e ^ 2 / 2 ≤ 2 * Nd ^ 4 * D := by
    have h1 : e ^ 2 ≤ (2 * s * Nd ^ 2) ^ 2 := pow_le_pow_left₀ he0 he1 2
    have h2 : (2 * s * Nd ^ 2) ^ 2 = 4 * Nd ^ 4 * s ^ 2 := by ring
    have h3 : Nd ^ 4 * s ^ 2 ≤ Nd ^ 4 * D := mul_le_mul_of_nonneg_left F8 (by positivity)
    linarith
  have hRe : |(e - 2 * s * a ^ 2) + e ^ 2 / 2 - (X + 2 * a * b) * (X - 2 * a * b) / 2| ≤
      4 * N ^ 2 / δ ^ 3 * (1 + 1 / δ) * D + 2 * Nd ^ 4 * D +
        (A + 2 * Nd) * (2 * (C4 * N) + γ * N / δ ^ 2) * D / 2 := by
    have h1 := abs_sub ((e - 2 * s * a ^ 2) + e ^ 2 / 2) ((X + 2 * a * b) * (X - 2 * a * b) / 2)
    have h2 := abs_add_le (e - 2 * s * a ^ 2) (e ^ 2 / 2)
    have h3 : |e ^ 2 / 2| = e ^ 2 / 2 := abs_of_nonneg (by positivity)
    have h4 : |(X + 2 * a * b) * (X - 2 * a * b) / 2| =
        |(X + 2 * a * b) * (X - 2 * a * b)| / 2 := by
      rw [abs_div, abs_two]
    linarith
  -- imaginary part
  have hIm : |RX + e * X| ≤ C4 * N * D + 2 * Nd ^ 2 * A * D := by
    have hRX2 : |RX| ≤ C4 * N * D := hRX'.trans (mul_le_mul_of_nonneg_left F2 hCr0)
    have heX : |e * X| ≤ 2 * Nd ^ 2 * A * D := by
      rw [abs_mul, abs_of_nonneg he0]
      calc e * |X| ≤ (2 * s * Nd ^ 2) * (A * (β + s)) :=
            mul_le_mul he1 hXu (abs_nonneg _) (by positivity)
        _ = 2 * Nd ^ 2 * A * (s * (β + s)) := by ring
        _ ≤ 2 * Nd ^ 2 * A * D := mul_le_mul_of_nonneg_left F5 (by positivity)
    linarith [abs_add_le RX (e * X)]
  have hK : Kall N δ γ C4 cs = 4 * (Real.exp (2 * Nd ^ 2) + 3) * (2 * Nd ^ 2 + A) ^ 3 +
      4 * N ^ 2 / δ ^ 3 * (1 + 1 / δ) + 2 * Nd ^ 4 +
      (2 * (C4 * N) + γ * N / δ ^ 2) * (A + 2 * Nd) / 2 + C4 * N + 2 * Nd ^ 2 * A := by
    rw [Kall, ← hA, ← hNd]; ring
  rw [hK]
  have htot := norm_add_le (Complex.exp w - 1 - w - w ^ 2 / 2)
    ((((e - 2 * s * a ^ 2) + e ^ 2 / 2 - (X + 2 * a * b) * (X - 2 * a * b) / 2 : ℝ) : ℂ) +
      I * ((RX + e * X : ℝ) : ℂ))
  have hs2 := hsplit ((e - 2 * s * a ^ 2) + e ^ 2 / 2 - (X + 2 * a * b) * (X - 2 * a * b) / 2)
    (RX + e * X)
  have e : (4 * (Real.exp (2 * Nd ^ 2) + 3) * (2 * Nd ^ 2 + A) ^ 3 +
      4 * N ^ 2 / δ ^ 3 * (1 + 1 / δ) + 2 * Nd ^ 4 +
      (2 * (C4 * N) + γ * N / δ ^ 2) * (A + 2 * Nd) / 2 + C4 * N + 2 * Nd ^ 2 * A) * D =
      4 * (Real.exp (2 * Nd ^ 2) + 3) * (2 * Nd ^ 2 + A) ^ 3 * D +
      (4 * N ^ 2 / δ ^ 3 * (1 + 1 / δ) * D + 2 * Nd ^ 4 * D +
        (A + 2 * Nd) * (2 * (C4 * N) + γ * N / δ ^ 2) * D / 2) +
      (C4 * N * D + 2 * Nd ^ 2 * A * D) := by ring
  rw [e]
  linarith

/-! ### The generator estimate -/

lemma Kall_nonneg {N δ γ C4 cs : ℝ} (hN : 0 ≤ N) (hδ : 0 < δ) (hγ : 0 < γ) (hC4 : 0 ≤ C4)
    (hcs : 0 ≤ cs) : 0 ≤ Kall N δ γ C4 cs := by
  unfold Kall; positivity

lemma abs_b0_le (h : IsGenTest σ δ R M) : |b0 σ| ≤ 1 / δ ^ 2 * N1 σ := by
  refine h.abs_integral_mul_le (fun z hz1 _ => ?_)
  have hzn : δ ≤ ‖z‖ := hz1.trans (Complex.im_le_norm z)
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_div, norm_one, norm_pow]
  exact div_le_div_of_nonneg_left zero_le_one (by have := h.pos; positivity)
    (pow_le_pow_left₀ h.pos.le hzn 2)

lemma rpow_half_nat {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : s ^ ((n : ℝ) / 2) = √s ^ n := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs]; congr 1; ring

lemma rpow_one_add_half_nat {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    s ^ (1 + (n : ℝ) / 2) = √s ^ (n + 2) := by
  rw [← rpow_half_nat hs (n + 2)]; congr 1; push_cast; ring

lemma timeIntegral_abs_mul_le {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) (y : ℝ) :
    (∫ r in (0 : ℝ)..s, |W r|) * y ≤ ((∫ r in (0 : ℝ)..s, W r ^ 2) + s * y ^ 2) / 2 := by
  rw [← intervalIntegral.integral_mul_const]
  have h1 : ∫ r in (0 : ℝ)..s, |W r| * y ≤ ∫ r in (0 : ℝ)..s, (W r ^ 2 + y ^ 2) / 2 := by
    refine intervalIntegral.integral_mono_on hs ?_ ?_ (fun r _ => ?_)
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
    · nlinarith [sq_nonneg (|W r| - y), sq_abs (W r)]
  have h2 : ∫ r in (0 : ℝ)..s, (W r ^ 2 + y ^ 2) / 2 = ((∫ r in (0 : ℝ)..s, W r ^ 2) + s * y ^ 2) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  linarith

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

lemma integral_affine_B (hB : IsPreBrownianReal B P) (t : ℝ≥0) (c1 c2 : ℝ) :
    ∫ ω, (c1 * B t ω + c2 * (B t ω ^ 2 - t)) ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have i1 : Integrable (fun ω => B t ω) P := hB.integrable_eval t
  have i2 : Integrable (fun ω => B t ω ^ 2) P := by
    have := integrable_pow hB t 2
    simpa [sq_abs] using this
  have i3 : Integrable (fun ω => B t ω ^ 2 - (t : ℝ)) P := i2.sub (integrable_const _)
  rw [integral_add (i1.const_mul c1) (i3.const_mul c2),
    integral_const_mul, integral_const_mul, integral_sub i2 (integrable_const _),
    QuantumZipper.integral_eq_zero hB, QuantumZipper.integral_sq hB, integral_const]
  simp

lemma integrable_affine_B (hB : IsPreBrownianReal B P) (t : ℝ≥0) (c1 c2 : ℝ) :
    Integrable (fun ω => c1 * B t ω + c2 * (B t ω ^ 2 - t)) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have i1 : Integrable (fun ω => B t ω) P := hB.integrable_eval t
  have i2 : Integrable (fun ω => B t ω ^ 2) P := by
    have := integrable_pow hB t 2
    simpa [sq_abs] using this
  exact (i1.const_mul c1).add ((i2.sub (integrable_const _)).const_mul c2)

/-- The constant `cX` of the crude bound on `X_s - X_0`. -/
def cX (κ δ : ℝ) : ℝ := 4 / (√κ * δ ^ 2) + 2 * Qc (√κ) / δ ^ 2

/-- The Gaussian-moment constant. -/
def CD (κ : ℝ) : ℝ :=
  gaussianAbsMoment 3 + gaussianAbsMoment 4 + gaussianAbsMoment 1 + gaussianAbsMoment 2
    + √κ * gaussianAbsMoment 1 + κ * gaussianAbsMoment 2 + 1

/-- The explicit constant of the generator estimate. -/
def Cgen (σ : ℂ → ℝ) (κ δ R : ℝ) : ℝ :=
  Kall (N1 σ) δ (√κ) (max (OnePointExpansion.C₄ κ δ R) 0) (cX κ δ) * CD κ

/-- The characteristic functional `Ψ_s(σ) = E exp(i X_s(σ) - E_s(σ)/2)` along the reverse
SLE flow driven by `W = √κ B`. -/
def Psi (κ : ℝ) (σ : ℂ → ℝ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (s : ℝ) : ℂ :=
  ∫ ω, Complex.exp (I * (Xs κ σ (drive κ B ω) s : ℂ) - (Es σ (drive κ B ω) s : ℂ) / 2) ∂P

/-- **The generator estimate.** For `0 ≤ s ≤ 1`,
`‖Ψ_s(σ) - exp(i X_0(σ) - E_0(σ)/2)‖ ≤ exp(-E_0(σ)/2) · Cgen · s^{3/2}`. -/
theorem norm_Psi_sub_le (h : IsGenTest σ δ R M) {κ : ℝ} (hκ : 0 < κ) (hB : IsBrownianReal B P)
    (hmeas : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖Psi κ σ B P s - Complex.exp (I * (X0 κ σ : ℂ) - (E0 σ : ℂ) / 2)‖ ≤
      Real.exp (-E0 σ / 2) * Cgen σ κ δ R * s ^ ((3 : ℝ) / 2) := by
  have hPB := hB.toIsPreBrownianReal
  have : IsProbabilityMeasure P := hPB.isGaussianProcess.isProbabilityMeasure
  have hδ := h.pos
  have hγ : 0 < √κ := Real.sqrt_pos.mpr hκ
  have hN := N1_nonneg σ
  have hcs : 0 ≤ cX κ δ := by have := Qc_pos hκ; unfold cX; positivity
  have hC4 : 0 ≤ max (OnePointExpansion.C₄ κ δ R) 0 := le_max_right _ _
  set K := Kall (N1 σ) δ (√κ) (max (OnePointExpansion.C₄ κ δ R) 0) (cX κ δ) with hKdef
  have hK0 : 0 ≤ K := Kall_nonneg hN hδ hγ hC4 hcs
  -- the random quantities
  have hts : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs
  let bF : Ω → ℝ := fun ω => B s.toNNReal ω
  let Xf : Ω → ℝ := fun ω => Xs κ σ (drive κ B ω) s - X0 κ σ
  let ef : Ω → ℝ := fun ω => -(Es σ (drive κ B ω) s - E0 σ) / 2
  let I1 : Ω → ℝ := fun ω => ∫ r in (0 : ℝ)..s, |B r.toNNReal ω| ^ 1
  let I2 : Ω → ℝ := fun ω => ∫ r in (0 : ℝ)..s, |B r.toNNReal ω| ^ 2
  let Df : Ω → ℝ := fun ω => |bF ω| ^ 3 + |bF ω| ^ 4 + s * |bF ω| + s * |bF ω| ^ 2 +
    √κ * I1 ω + κ * I2 ω + s * √s
  let Pc : Ω → ℂ := fun ω => (((2 * a0 σ ^ 2 * (s - bF ω ^ 2)) : ℝ) : ℂ) +
    I * (((-2 * a0 σ * bF ω - √κ * b0 σ * (bF ω ^ 2 - s)) : ℝ) : ℂ)
  -- pointwise bound
  have hpt : ∀ ω, ‖Complex.exp (ef ω + I * Xf ω) - 1 - Pc ω‖ ≤ K * Df ω := by
    intro ω
    have hW := continuous_drive κ hc ω
    have hWB : ∀ r, drive κ B ω r = √κ * (fun r : ℝ => B r.toNNReal ω) r := fun r => rfl
    have hm : ∫ r in (0 : ℝ)..s, |drive κ B ω r| = √κ * I1 ω := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [hWB, abs_mul, abs_of_pos hγ, pow_one]
    have hV : ∫ r in (0 : ℝ)..s, drive κ B ω r ^ 2 = κ * I2 ω := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [hWB, mul_pow, Real.sq_sqrt hκ.le, sq_abs]
    have hm0 : 0 ≤ ∫ r in (0 : ℝ)..s, |drive κ B ω r| :=
      intervalIntegral.integral_nonneg hs fun r _ => abs_nonneg _
    have hV0 : 0 ≤ ∫ r in (0 : ℝ)..s, drive κ B ω r ^ 2 :=
      intervalIntegral.integral_nonneg hs fun r _ => sq_nonneg _
    have hEz := Es_zero h hW
    have hRX := abs_Xs_sub_X0_sub_expansion_le h hκ hW hWB hs hs1
    have hRX' : |Xf ω - (-2 * a0 σ * bF ω - √κ * b0 σ * (bF ω ^ 2 - s))| ≤
        max (OnePointExpansion.C₄ κ δ R) 0 *
          (|bF ω| ^ 3 + s * |bF ω| + (∫ r in (0 : ℝ)..s, |drive κ B ω r|) + s ^ 2) * N1 σ := by
      refine hRX.trans ?_
      apply mul_le_mul_of_nonneg_right _ hN
      apply mul_le_mul_of_nonneg_right (le_max_left _ _)
      have := abs_nonneg (bF ω)
      positivity
    have hX := abs_Xs_sub_X0_le h hκ hW hWB hs
    have he0 : 0 ≤ ef ω := by
      have := Es_sub_nonpos h hW hs hs1; rw [hEz] at this; show 0 ≤ -(_ - _) / 2; linarith
    have he1 : ef ω ≤ 2 * s * (N1 σ / δ) ^ 2 := by
      have := abs_Es_sub_le h hW hs hs1; rw [hEz] at this
      show -(_ - _) / 2 ≤ _
      linarith [neg_abs_le (Es σ (drive κ B ω) s - E0 σ)]
    have hRE : |ef ω - 2 * s * a0 σ ^ 2| ≤
        4 * N1 σ ^ 2 / δ ^ 3 * ((∫ r in (0 : ℝ)..s, |drive κ B ω r|) + s ^ 2 / δ) := by
      have := abs_Es_sub_add_le h hW hs hs1; rw [hEz] at this
      have e : ef ω - 2 * s * a0 σ ^ 2 = -(Es σ (drive κ B ω) s - E0 σ + 4 * s * a0 σ ^ 2) / 2 := by
        show -(_ - _) / 2 - _ = _; ring
      rw [e, abs_div, abs_neg, abs_two]
      have h8 := div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2)
      calc _ ≤ 8 * N1 σ ^ 2 / δ ^ 3 * ((∫ r in (0 : ℝ)..s, |drive κ B ω r|) + s ^ 2 / δ) / 2 := h8
        _ = _ := by ring
    have ha : |a0 σ| ≤ N1 σ / δ := by
      have := abs_a0_le h; rwa [one_div_mul_eq_div] at this
    have hbb : |b0 σ| ≤ N1 σ / δ ^ 2 := by
      have := abs_b0_le h; rwa [one_div_mul_eq_div] at this
    have hmβ := timeIntegral_abs_mul_le hW hs |bF ω|
    rw [sq_abs] at hmβ
    have key := pointwise_key hN hδ hγ hC4 hcs ha hbb hs hs1 hm0 hV0
      (by rw [sq_abs]; exact hmβ) hX hRX' he0 he1 hRE
    rw [hm, hV] at key
    exact key
  -- measurability and integrability
  have hXm : Measurable fun ω => Xs κ σ (drive κ B ω) s := measurable_Xs_drive h κ hmeas hc hs
  have hEm : Measurable fun ω => Es σ (drive κ B ω) s := measurable_Es_drive h κ hmeas hc hs hs1
  set F : Ω → ℂ := fun ω => Complex.exp (I * (Xs κ σ (drive κ B ω) s : ℂ) -
    (Es σ (drive κ B ω) s : ℂ) / 2) with hFdef
  set w0 : ℂ := I * (X0 κ σ : ℂ) - (E0 σ : ℂ) / 2 with hw0
  have hFeq : ∀ ω, F ω = Complex.exp w0 * Complex.exp (ef ω + I * Xf ω) := by
    intro ω
    rw [← Complex.exp_add]
    simp only [hFdef, hw0, ef, Xf]
    congr 1; push_cast; ring
  have hFm : AEStronglyMeasurable F P :=
    (Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp hXm)).sub
      ((Complex.measurable_ofReal.comp hEm).div_const 2))).aestronglyMeasurable
  have hFb : ∀ ω, ‖F ω‖ ≤ Real.exp (-E0 σ / 2 + 2 * (N1 σ / δ) ^ 2) := by
    intro ω
    have hW := continuous_drive κ hc ω
    have := abs_Es_sub_le h hW hs hs1
    rw [Es_zero h hW] at this
    simp only [hFdef, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re]
    have h4 : 4 * s * (N1 σ / δ) ^ 2 ≤ 4 * (N1 σ / δ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hs1 (by positivity : (0 : ℝ) ≤ 4 * (N1 σ / δ) ^ 2)
      linarith
    linarith [neg_abs_le (Es σ (drive κ B ω) s - E0 σ)]
  have hFint : Integrable F P :=
    Integrable.mono' (integrable_const _) hFm (Eventually.of_forall hFb)
  have hPc1 : Integrable (fun ω => 2 * a0 σ ^ 2 * (s - bF ω ^ 2)) P := by
    have := integrable_affine_B hPB s.toNNReal 0 (-2 * a0 σ ^ 2)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hts, bF]; ring
  have hPc2 : Integrable (fun ω => -2 * a0 σ * bF ω - √κ * b0 σ * (bF ω ^ 2 - s)) P := by
    have := integrable_affine_B hPB s.toNNReal (-2 * a0 σ) (-(√κ * b0 σ))
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hts, bF]; ring
  have hPint : Integrable Pc P := hPc1.ofReal.add (hPc2.ofReal.const_mul I)
  have hEP : ∫ ω, Pc ω ∂P = 0 := by
    have e1 : ∫ ω, 2 * a0 σ ^ 2 * (s - bF ω ^ 2) ∂P = 0 := by
      rw [← integral_affine_B hPB s.toNNReal 0 (-2 * a0 σ ^ 2)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hts, bF]; ring
    have e2 : ∫ ω, (-2 * a0 σ * bF ω - √κ * b0 σ * (bF ω ^ 2 - s)) ∂P = 0 := by
      rw [← integral_affine_B hPB s.toNNReal (-2 * a0 σ) (-(√κ * b0 σ))]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hts, bF]; ring
    have j1 : Integrable (fun ω => (((2 * a0 σ ^ 2 * (s - bF ω ^ 2)) : ℝ) : ℂ)) P := hPc1.ofReal
    have j2 : Integrable (fun ω => I * (((-2 * a0 σ * bF ω - √κ * b0 σ * (bF ω ^ 2 - s)) : ℝ) : ℂ))
        P := hPc2.ofReal.const_mul I
    show ∫ ω, ((((2 * a0 σ ^ 2 * (s - bF ω ^ 2)) : ℝ) : ℂ) +
      I * (((-2 * a0 σ * bF ω - √κ * b0 σ * (bF ω ^ 2 - s)) : ℝ) : ℂ)) ∂P = 0
    rw [integral_add j1 j2, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      e1, e2]
    simp
  -- Df integrable
  have hbn : ∀ n : ℕ, Integrable (fun ω => |bF ω| ^ n) P := fun n => integrable_pow hPB _ n
  have hI1 := integrable_timeIntegral_abs_pow hPB hmeas hc 1 hs
  have hI2 := integrable_timeIntegral_abs_pow hPB hmeas hc 2 hs
  have hb1 : Integrable (fun ω => |bF ω|) P := by simpa using hbn 1
  have j1 : Integrable (fun ω => |bF ω| ^ 3 + |bF ω| ^ 4) P := (hbn 3).add (hbn 4)
  have j2 : Integrable (fun ω => |bF ω| ^ 3 + |bF ω| ^ 4 + s * |bF ω|) P := j1.add (hb1.const_mul s)
  have j3 : Integrable (fun ω => |bF ω| ^ 3 + |bF ω| ^ 4 + s * |bF ω| + s * |bF ω| ^ 2) P :=
    j2.add ((hbn 2).const_mul s)
  have j4 : Integrable (fun ω => |bF ω| ^ 3 + |bF ω| ^ 4 + s * |bF ω| + s * |bF ω| ^ 2 +
      √κ * I1 ω) P := j3.add (hI1.const_mul _)
  have j5 : Integrable (fun ω => |bF ω| ^ 3 + |bF ω| ^ 4 + s * |bF ω| + s * |bF ω| ^ 2 +
      √κ * I1 ω + κ * I2 ω) P := j4.add (hI2.const_mul _)
  have hDint : Integrable Df P := j5.add (integrable_const _)
  -- the reduction
  have hred : Psi κ σ B P s - Complex.exp w0 =
      ∫ ω, Complex.exp w0 * (Complex.exp (ef ω + I * Xf ω) - 1 - Pc ω) ∂P := by
    have e : (fun ω => Complex.exp w0 * (Complex.exp (ef ω + I * Xf ω) - 1 - Pc ω)) =
        fun ω => F ω - Complex.exp w0 - Complex.exp w0 * Pc ω := by
      funext ω; rw [hFeq]; ring
    have j6 : Integrable (fun ω => F ω - Complex.exp w0) P := hFint.sub (integrable_const _)
    have j7 : Integrable (fun ω => Complex.exp w0 * Pc ω) P := hPint.const_mul _
    rw [e, integral_sub j6 j7, integral_sub hFint (integrable_const _), integral_const_mul, hEP,
      integral_const]
    simp [Psi, hFdef]
  have hnorm0 : ‖Complex.exp w0‖ = Real.exp (-E0 σ / 2) := by
    rw [Complex.norm_exp, hw0]
    congr 1
    simp [Complex.div_ofNat_re]
    ring
  have hbound : ‖Psi κ σ B P s - Complex.exp w0‖ ≤ Real.exp (-E0 σ / 2) * K * ∫ ω, Df ω ∂P := by
    rw [hred]
    have := norm_integral_le_of_norm_le (hDint.const_mul (Real.exp (-E0 σ / 2) * K))
      (Eventually.of_forall fun ω => (show ‖Complex.exp w0 * (Complex.exp (ef ω + I * Xf ω) - 1 - Pc ω)‖
        ≤ Real.exp (-E0 σ / 2) * K * Df ω by
          rw [norm_mul, hnorm0, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hpt ω) (Real.exp_pos _).le))
    exact this.trans (le_of_eq (integral_const_mul _ _))
  -- the expectation of Df
  have hq0 : 0 ≤ √s := Real.sqrt_nonneg s
  have hq1 : √s ≤ 1 := Real.sqrt_le_one.mpr hs1
  have hqs : √s ^ 2 = s := Real.sq_sqrt hs
  have hmom : ∀ n : ℕ, ∫ ω, |bF ω| ^ n ∂P ≤ gaussianAbsMoment n * √s ^ n := by
    intro n
    have := integral_abs_pow_le hPB s.toNNReal n
    rwa [hts, rpow_half_nat hs] at this
  have htmom : ∀ n : ℕ, ∫ ω, (∫ r in (0 : ℝ)..s, |B r.toNNReal ω| ^ n) ∂P ≤
      gaussianAbsMoment n * √s ^ (n + 2) := by
    intro n
    have := integral_integral_abs_pow_le hPB hmeas hc n s hs
    rwa [rpow_one_add_half_nat hs] at this
  have hED : ∫ ω, Df ω ∂P ≤ CD κ * √s ^ 3 := by
    have eD : ∫ ω, Df ω ∂P = (∫ ω, |bF ω| ^ 3 ∂P) + (∫ ω, |bF ω| ^ 4 ∂P) +
        s * (∫ ω, |bF ω| ^ 1 ∂P) + s * (∫ ω, |bF ω| ^ 2 ∂P) + √κ * (∫ ω, I1 ω ∂P) +
        κ * (∫ ω, I2 ω ∂P) + s * √s := by
      show ∫ ω, (|bF ω| ^ 3 + |bF ω| ^ 4 + s * |bF ω| + s * |bF ω| ^ 2 +
        √κ * I1 ω + κ * I2 ω + s * √s) ∂P = _
      rw [integral_add j5 (integrable_const _), integral_add j4 (hI2.const_mul _),
        integral_add j3 (hI1.const_mul _), integral_add j2 ((hbn 2).const_mul s),
        integral_add j1 (hb1.const_mul s), integral_add (hbn 3) (hbn 4),
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const]
      simp [I1, I2]
    rw [eD]
    have m1 := hmom 1
    have m2 := hmom 2
    have m3 := hmom 3
    have m4 := hmom 4
    have t1 := htmom 1
    have t2 := htmom 2
    have g1 := gaussianAbsMoment_nonneg 1
    have g2 := gaussianAbsMoment_nonneg 2
    have g3 := gaussianAbsMoment_nonneg 3
    have g4 := gaussianAbsMoment_nonneg 4
    generalize hq : √s = q at *
    subst hqs
    have hq4 : q ^ 4 ≤ q ^ 3 := by nlinarith [pow_nonneg hq0 3]
    have hq5 : q ^ 5 ≤ q ^ 3 := by nlinarith [pow_nonneg hq0 3, pow_nonneg hq0 4]
    have hq6 : q ^ 6 ≤ q ^ 3 := by nlinarith [pow_nonneg hq0 3, pow_nonneg hq0 4, pow_nonneg hq0 5]
    unfold CD
    have k1 : q ^ 2 * ∫ ω, |bF ω| ^ 1 ∂P ≤ gaussianAbsMoment 1 * q ^ 3 := by
      have := mul_le_mul_of_nonneg_left m1 (sq_nonneg q)
      linarith [show q ^ 2 * (gaussianAbsMoment 1 * q ^ 1) = gaussianAbsMoment 1 * q ^ 3 by ring]
    have k2 : q ^ 2 * ∫ ω, |bF ω| ^ 2 ∂P ≤ gaussianAbsMoment 2 * q ^ 3 := by
      have := mul_le_mul_of_nonneg_left m2 (sq_nonneg q)
      have := mul_le_mul_of_nonneg_left hq4 g2
      linarith [show q ^ 2 * (gaussianAbsMoment 2 * q ^ 2) = gaussianAbsMoment 2 * q ^ 4 by ring]
    have k3 : √κ * ∫ ω, I1 ω ∂P ≤ √κ * gaussianAbsMoment 1 * q ^ 3 := by
      have := mul_le_mul_of_nonneg_left t1 hγ.le
      linarith [show √κ * (gaussianAbsMoment 1 * q ^ (1 + 2)) = √κ * gaussianAbsMoment 1 * q ^ 3 by ring]
    have k4 : κ * ∫ ω, I2 ω ∂P ≤ κ * gaussianAbsMoment 2 * q ^ 3 := by
      have := mul_le_mul_of_nonneg_left t2 hκ.le
      have := mul_le_mul_of_nonneg_left hq4 (mul_nonneg hκ.le g2)
      linarith [show κ * (gaussianAbsMoment 2 * q ^ (2 + 2)) = κ * gaussianAbsMoment 2 * q ^ 4 by ring]
    have k5 : ∫ ω, |bF ω| ^ 4 ∂P ≤ gaussianAbsMoment 4 * q ^ 3 := by
      have := mul_le_mul_of_nonneg_left hq4 g4
      linarith
    have k6 : q ^ 2 * q = q ^ 3 := by ring
    nlinarith
  have hs32 : s ^ ((3 : ℝ) / 2) = √s ^ 3 := by
    have := rpow_half_nat hs 3; norm_num at this; exact this
  rw [hs32]
  refine hbound.trans ?_
  have hEK : 0 ≤ Real.exp (-E0 σ / 2) * K := mul_nonneg (Real.exp_pos _).le hK0
  calc Real.exp (-E0 σ / 2) * K * ∫ ω, Df ω ∂P ≤ Real.exp (-E0 σ / 2) * K * (CD κ * √s ^ 3) :=
        mul_le_mul_of_nonneg_left hED hEK
    _ = Real.exp (-E0 σ / 2) * Cgen σ κ δ R * √s ^ 3 := by rw [Cgen, ← hKdef]; ring

end Prob

end Generator
end QuantumZipper
