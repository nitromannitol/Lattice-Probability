/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CoordRegHarm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CoordRegPush
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The pulled-back Neumann kernel of an unzip map (helper for RC3)

For `f = revMap W T` and `u, v ∈ ℍ`, `u ≠ v`,
`neumannH (f u) (f v) = neumannH u v + hK u v` (`neumannH_revMap_eq`), where
`hK u v = −log ‖(f u − f v)/(u − v)‖ − log ‖f u − conj (f v)‖ + log ‖u − conj v‖`
(with the difference quotient read as `dslope f v u`, which is `f' v` at `u = v`).

* `hK` is symmetric (`hK_symm`) and, in each variable, `log ‖·‖` of functions holomorphic and
  zero-free on `ℍ` (`f` is injective and `f' ≠ 0`), hence harmonic. The mean value property on
  circles inside `ℍ` (`integral_hK_circleUnif`) is Jensen's formula for zero-free functions
  (`AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`, mathlib).
* Bounds: `|hK u v| ≤ A + 3 · (|log Im u| + |log Im v|)` on bounded sets (`abs_hK_le`; the
  factor 3 is the number of `log` terms in `hK`), from the two-point bounds of `TwoPoint` (§1.3
  of `AUDIT3.md`); and the folded-circle average of `|log Im|` is at most `C + |log Im z|`
  (`integral_abs_log_im_fc_le`).

The decomposition into a Neumann part and a part harmonic in each variable is our own device
(no published source treats circle-average regularization of a pulled-back field); it only uses
the mean value property of harmonic functions.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace CoordReg

open SmoothConv

/-! ## Mean value property on circles -/

theorem integral_circleUnif_eq_circleAverage {g : ℂ → ℝ} (hg : Measurable g) (c : ℂ) (R : ℝ) :
    ∫ z, g z ∂circleUnif c R = Real.circleAverage g c R := by
  rw [integral_circleUnif_Ico hg, setIntegral_Ico_eq_intervalIntegral, Real.circleAverage_def,
    smul_eq_mul]

theorem integral_log_norm_circleUnif_of_analytic {F : ℂ → ℂ} (hFm : Measurable F) {c : ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hF : AnalyticOnNhd ℂ F (closedBall c R))
    (hF0 : ∀ u ∈ closedBall c R, F u ≠ 0) :
    ∫ z, Real.log ‖F z‖ ∂circleUnif c R = Real.log ‖F c‖ := by
  rw [integral_circleUnif_eq_circleAverage (show Measurable fun z => Real.log ‖F z‖ from
    Real.measurable_log.comp hFm.norm)]
  rw [← abs_of_nonneg hR] at hF hF0
  exact AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hF hF0

theorem ae_mem_closedBall_circleUnif (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ z ∂circleUnif c R, z ∈ closedBall c R := by
  filter_upwards [ae_circleUnif_sc c R] with z hz
  rw [mem_closedBall, dist_eq_norm, hz, abs_of_nonneg hR]

theorem integrable_circleUnif_of_continuousOn {g : ℂ → ℝ} (hgm : Measurable g) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hg : ContinuousOn g (closedBall c R)) : Integrable g (circleUnif c R) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg
  exact Integrable.of_bound hgm.aestronglyMeasurable M
    ((ae_mem_closedBall_circleUnif c hR).mono fun z hz => hM z hz)

/-! ## The harmonic correction -/

variable {W : ℝ → ℝ} {T : ℝ}

/-- The harmonic correction of the pulled-back Neumann kernel. -/
def hK (W : ℝ → ℝ) (T : ℝ) (u v : ℂ) : ℝ :=
  -Real.log ‖dslope (revMap W T) v u‖ - Real.log ‖revMap W T u - conj (revMap W T v)‖ +
    Real.log ‖u - conj v‖

theorem dslope_eq_ite (f : ℂ → ℂ) (v : ℂ) :
    dslope f v = fun u => if u = v then deriv f v else (f u - f v) / (u - v) := by
  funext u
  by_cases h : u = v
  · subst h; simp [dslope_same]
  · simp [dslope_of_ne _ h, slope_def_field, h]

theorem measurable_dslope {f : ℂ → ℂ} (hf : Measurable f) (v : ℂ) : Measurable (dslope f v) := by
  rw [dslope_eq_ite]
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
    ((hf.sub_const _).div (measurable_id.sub_const _))

theorem dslope_symm (f : ℂ → ℂ) (u v : ℂ) : dslope f v u = dslope f u v := by
  by_cases h : u = v
  · subst h; rfl
  · rw [dslope_of_ne _ h, dslope_of_ne _ (Ne.symm h), slope_comm]

variable (hW : Continuous W) (hT : 0 ≤ T)
include hW hT

theorem hK_symm {u v : ℂ} : hK W T u v = hK W T v u := by
  unfold hK
  rw [dslope_symm, norm_sub_conj_comm (revMap W T u), norm_sub_conj_comm u]

theorem neumannH_revMap_eq {u v : ℂ} (hu : u ∈ H) (hv : v ∈ H) (huv : u ≠ v) :
    neumannH (revMap W T u) (revMap W T v) = neumannH u v + hK W T u v := by
  have h1 : revMap W T u - revMap W T v ≠ 0 :=
    sub_ne_zero.2 fun h => huv (injOn_revMap W hW hT hu hv h)
  have h2 : u - v ≠ 0 := sub_ne_zero.2 huv
  unfold hK neumannH
  rw [dslope_of_ne _ huv, slope_def_field, norm_div,
    Real.log_div (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h2)]
  ring

theorem dslope_revMap_ne_zero {u v : ℂ} (hu : u ∈ H) (hv : v ∈ H) :
    dslope (revMap W T) v u ≠ 0 := by
  by_cases h : u = v
  · subst h; rw [dslope_same]; exact deriv_revMap_ne_zero W hW hT hu
  · rw [dslope_of_ne _ h, slope_def_field]
    exact div_ne_zero (sub_ne_zero.2 fun e => h (injOn_revMap W hW hT hu hv e))
      (sub_ne_zero.2 h)

theorem analyticOnNhd_dslope_revMap {v : ℂ} (hv : v ∈ H) :
    AnalyticOnNhd ℂ (dslope (revMap W T) v) H :=
  ((Complex.differentiableOn_dslope (isOpen_H.mem_nhds hv)).2
    (differentiableOn_revMap W hW hT)).analyticOnNhd isOpen_H

omit hW hT in
theorem im_add_im_le_norm_sub_conj' (x w : ℂ) : x.im + w.im ≤ ‖x - conj w‖ := by
  have h : (x - conj w).im = x.im + w.im := by simp
  rw [← h]; exact (le_abs_self _).trans (Complex.abs_im_le_norm _)

/-- **Mean value property** of `hK` in the first variable on circles inside `ℍ`. -/
theorem integral_hK_circleUnif {v : ℂ} (hv : v ∈ H) {z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hzr : closedBall z r ⊆ H) :
    ∫ u, hK W T u v ∂circleUnif z r = hK W T z v := by
  have hfm := TwoPoint.measurable_revMap hW hT
  have hdiff := differentiableOn_revMap W hW hT
  -- the three zero-free holomorphic factors
  set F1 := dslope (revMap W T) v
  set F2 : ℂ → ℂ := fun u => revMap W T u - conj (revMap W T v)
  set F3 : ℂ → ℂ := fun u => u - conj v
  have hF1m : Measurable F1 := measurable_dslope hfm v
  have hF2m : Measurable F2 := hfm.sub_const _
  have hF3m : Measurable F3 := measurable_id.sub_const _
  have hF1a : AnalyticOnNhd ℂ F1 (closedBall z r) := (analyticOnNhd_dslope_revMap hW hT hv).mono hzr
  have hF2a : AnalyticOnNhd ℂ F2 (closedBall z r) :=
    ((hdiff.sub_const _).analyticOnNhd isOpen_H).mono hzr
  have hF3a : AnalyticOnNhd ℂ F3 (closedBall z r) :=
    (differentiable_id.sub_const _).differentiableOn.analyticOnNhd isOpen_univ |>.mono
      (subset_univ _)
  have hF1z : ∀ u ∈ closedBall z r, F1 u ≠ 0 := fun u hu =>
    dslope_revMap_ne_zero hW hT (hzr hu) hv
  have hF2z : ∀ u ∈ closedBall z r, F2 u ≠ 0 := fun u hu h => by
    have := im_add_im_le_norm_sub_conj' (revMap W T u) (revMap W T v)
    have a1 := TwoPoint.im_revMap_pos hW (hzr hu) hT
    have a2 := TwoPoint.im_revMap_pos hW hv hT
    simp only [F2] at h
    rw [h, norm_zero] at this; linarith
  have hF3z : ∀ u ∈ closedBall z r, F3 u ≠ 0 := fun u hu h => by
    have := im_add_im_le_norm_sub_conj' u v
    have a1 : 0 < u.im := hzr hu
    have a2 : 0 < v.im := hv
    simp only [F3] at h
    rw [h, norm_zero] at this; linarith
  have i1 : Integrable (fun u => Real.log ‖F1 u‖) (circleUnif z r) :=
    integrable_circleUnif_of_continuousOn (Real.measurable_log.comp hF1m.norm) hr
      (hF1a.continuousOn.norm.log fun u hu => norm_ne_zero_iff.2 (hF1z u hu))
  have i2 : Integrable (fun u => Real.log ‖F2 u‖) (circleUnif z r) :=
    integrable_circleUnif_of_continuousOn (Real.measurable_log.comp hF2m.norm) hr
      (hF2a.continuousOn.norm.log fun u hu => norm_ne_zero_iff.2 (hF2z u hu))
  have i3 : Integrable (fun u => Real.log ‖F3 u‖) (circleUnif z r) :=
    integrable_circleUnif_of_continuousOn (Real.measurable_log.comp hF3m.norm) hr
      (hF3a.continuousOn.norm.log fun u hu => norm_ne_zero_iff.2 (hF3z u hu))
  have i1n : Integrable (fun u => -Real.log ‖F1 u‖) (circleUnif z r) := i1.neg
  have i12 : Integrable (fun u => -Real.log ‖F1 u‖ - Real.log ‖F2 u‖) (circleUnif z r) :=
    i1n.sub i2
  have e : (fun u => hK W T u v) = fun u =>
      -Real.log ‖F1 u‖ - Real.log ‖F2 u‖ + Real.log ‖F3 u‖ := rfl
  rw [e, integral_add i12 i3, integral_sub i1n i2, integral_neg,
    integral_log_norm_circleUnif_of_analytic hF1m hr hF1a hF1z,
    integral_log_norm_circleUnif_of_analytic hF2m hr hF2a hF2z,
    integral_log_norm_circleUnif_of_analytic hF3m hr hF3a hF3z]
  rfl

/-! ## Bounds -/

omit hW hT in
theorem abs_log_le_of_mem' {a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| :=
  TwoPoint.abs_log_le_of_mem ha hax hxb

/-- `|hK u v| ≤ A + 3 (|log Im u| + |log Im v|)` on bounded subsets of `ℍ`. -/
theorem abs_hK_le (R : ℝ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ H, ∀ v ∈ H, ‖u‖ ≤ R → ‖v‖ ≤ R →
    |hK W T u v| ≤ A + 3 * (|Real.log u.im| + |Real.log v.im|) := by
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hW hT R
  set M := Real.sqrt (R ^ 2 + 4 * T) with hM
  set B := max (max (2 * Bf) (2 * R)) 1 with hB
  refine ⟨|Real.log M| + 2 * |Real.log B|, by positivity, fun u hu v hv huR hvR => ?_⟩
  have hu0 : 0 < u.im := hu
  have hv0 : 0 < v.im := hv
  have hfu := TwoPoint.im_revMap_pos hW hu hT
  have hfv := TwoPoint.im_revMap_pos hW hv hT
  have hIu : u.im ≤ (revMap W T u).im := im_le_im_revMap W hW u hu hT
  have hIv : v.im ≤ (revMap W T v).im := im_le_im_revMap W hW v hv hT
  have hMu : (revMap W T u).im ≤ M := by
    have h1 := TwoPoint.im_revMap_sq_le hW hu hT
    have h2 : u.im ≤ R := (Complex.im_le_norm u).trans huR
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hMv : (revMap W T v).im ≤ M := by
    have h1 := TwoPoint.im_revMap_sq_le hW hv hT
    have h2 : v.im ≤ R := (Complex.im_le_norm v).trans hvR
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  -- term 1
  have t1 : |Real.log ‖dslope (revMap W T) v u‖| ≤
      |Real.log M| + |Real.log u.im| + |Real.log v.im| := by
    by_cases h : u = v
    · subst h
      rw [dslope_same]
      have := TwoPoint.abs_log_norm_deriv_revMap_le hW hT hu
        ((Complex.im_le_norm u).trans huR)
      linarith [abs_nonneg (Real.log u.im)]
    · have hd1 : revMap W T u - revMap W T v ≠ 0 :=
        sub_ne_zero.2 fun e => h (injOn_revMap W hW hT hu hv e)
      have hd2 : u - v ≠ 0 := sub_ne_zero.2 h
      have n1 : 0 < ‖revMap W T u - revMap W T v‖ := norm_pos_iff.2 hd1
      have n2 : 0 < ‖u - v‖ := norm_pos_iff.2 hd2
      rw [dslope_of_ne _ h, slope_def_field, norm_div, Real.log_div n1.ne' n2.ne']
      have lo := TwoPoint.twoPoint_lower_sq hW hu hv hT
      have up := TwoPoint.twoPoint_upper_sq hW hu hv hT
      have L1 := Real.log_le_log (mul_pos (pow_pos n2 2) (mul_pos hu0 hv0)) lo
      have L2 := Real.log_le_log (mul_pos (pow_pos n1 2) (mul_pos hu0 hv0)) up
      have e1 : Real.log (‖u - v‖ ^ 2 * (u.im * v.im)) =
          2 * Real.log ‖u - v‖ + (Real.log u.im + Real.log v.im) := by
        rw [Real.log_mul (pow_ne_zero 2 n2.ne') (mul_pos hu0 hv0).ne', Real.log_pow,
          Real.log_mul hu0.ne' hv0.ne']; push_cast; ring
      have e2 : Real.log (‖revMap W T u - revMap W T v‖ ^ 2 * (u.im * v.im)) =
          2 * Real.log ‖revMap W T u - revMap W T v‖ + (Real.log u.im + Real.log v.im) := by
        rw [Real.log_mul (pow_ne_zero 2 n1.ne') (mul_pos hu0 hv0).ne', Real.log_pow,
          Real.log_mul hu0.ne' hv0.ne']; push_cast; ring
      have e3 : Real.log (‖u - v‖ ^ 2 * ((revMap W T u).im * (revMap W T v).im)) =
          2 * Real.log ‖u - v‖ + (Real.log (revMap W T u).im + Real.log (revMap W T v).im) := by
        rw [Real.log_mul (pow_ne_zero 2 n2.ne') (mul_pos hfu hfv).ne', Real.log_pow,
          Real.log_mul hfu.ne' hfv.ne']; push_cast; ring
      have e4 : Real.log (‖revMap W T u - revMap W T v‖ ^ 2 *
          ((revMap W T u).im * (revMap W T v).im)) =
          2 * Real.log ‖revMap W T u - revMap W T v‖ +
            (Real.log (revMap W T u).im + Real.log (revMap W T v).im) := by
        rw [Real.log_mul (pow_ne_zero 2 n1.ne') (mul_pos hfu hfv).ne', Real.log_pow,
          Real.log_mul hfu.ne' hfv.ne']; push_cast; ring
      rw [e1, e4] at L1
      rw [e2, e3] at L2
      have a1 := Real.log_le_log hu0 hIu
      have a2 := Real.log_le_log hv0 hIv
      have a3 := Real.log_le_log hfu hMu
      have a4 := Real.log_le_log hfv hMv
      rw [abs_le]
      constructor <;>
        linarith [le_abs_self (Real.log M), neg_abs_le (Real.log M), le_abs_self (Real.log u.im),
          neg_abs_le (Real.log u.im), le_abs_self (Real.log v.im), neg_abs_le (Real.log v.im)]
  -- term 2
  have t2 : |Real.log ‖revMap W T u - conj (revMap W T v)‖| ≤ |Real.log u.im| + |Real.log B| := by
    refine abs_log_le_of_mem' hu0 ?_ ?_
    · have := im_add_im_le_norm_sub_conj' (revMap W T u) (revMap W T v)
      linarith
    · calc ‖revMap W T u - conj (revMap W T v)‖ ≤ ‖revMap W T u‖ + ‖conj (revMap W T v)‖ :=
            norm_sub_le _ _
        _ ≤ 2 * Bf := by rw [Complex.norm_conj]; linarith [hBf u hu huR, hBf v hv hvR]
        _ ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  -- term 3
  have t3 : |Real.log ‖u - conj v‖| ≤ |Real.log u.im| + |Real.log B| := by
    refine abs_log_le_of_mem' hu0 ?_ ?_
    · have := im_add_im_le_norm_sub_conj' u v
      linarith
    · calc ‖u - conj v‖ ≤ ‖u‖ + ‖conj v‖ := norm_sub_le _ _
        _ ≤ 2 * R := by rw [Complex.norm_conj]; linarith
        _ ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have b1 := abs_le.1 t1
  have b2 := abs_le.1 t2
  have b3 := abs_le.1 t3
  unfold hK
  rw [abs_le]
  constructor <;>
    linarith [abs_nonneg (Real.log u.im), abs_nonneg (Real.log v.im),
      abs_nonneg (Real.log M), abs_nonneg (Real.log B)]

omit hW hT in
/-- The folded-circle average of `|log Im|` at a point `z ∈ ℍ` and radius `r ≤ 1` is at most
`C₀ + |log Im z|`. -/
theorem integral_abs_log_im_fc_le (R : ℝ) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ z ∈ H, ‖z‖ ≤ R → ∀ r : ℝ,
    0 < r → r ≤ 1 → ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ C₀ + |Real.log z.im| := by
  set L := max (Real.log (R + 1)) 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨36 + Real.log 2 + L, by positivity, fun z hz hzR r hr hr1 => ?_⟩
  have hz0 : 0 < z.im := hz
  have hint : Integrable (fun u : ℂ => |Real.log u.im|) (foldedCircle z r) :=
    (TwoPoint.integrable_log_im_foldedCircle z hr).abs
  rcases le_or_gt r (z.im / 2) with hrz | hrz
  · -- the circle stays at height `≥ Im z / 2`
    have hfc : foldedCircle z r = circleUnif z r :=
      foldedCircle_eq_circleUnif_sc hr.le (by linarith)
    have hpt : ∀ᵐ u ∂foldedCircle z r, |Real.log u.im| ≤ |Real.log z.im| + Real.log 2 := by
      rw [hfc]
      filter_upwards [ae_circleUnif_sc z r] with u hu
      have hd : |u.im - z.im| ≤ r := by
        have := Complex.abs_im_le_norm (u - z)
        rw [hu, abs_of_pos hr, Complex.sub_im] at this; exact this
      have h1 : z.im / 2 ≤ u.im := by linarith [(abs_le.1 hd).1]
      have h2 : u.im ≤ 2 * z.im := by linarith [(abs_le.1 hd).2]
      have hu0 : 0 < u.im := by linarith
      have l1 := Real.log_le_log (by linarith) h1
      have l2 := Real.log_le_log hu0 h2
      rw [Real.log_div hz0.ne' two_ne_zero] at l1
      rw [Real.log_mul two_ne_zero hz0.ne'] at l2
      rw [abs_le]; constructor <;>
        linarith [le_abs_self (Real.log z.im), neg_abs_le (Real.log z.im)]
    calc ∫ u, |Real.log u.im| ∂foldedCircle z r ≤ ∫ _u, (|Real.log z.im| + Real.log 2)
          ∂foldedCircle z r := integral_mono_ae hint (integrable_const _) hpt
      _ = |Real.log z.im| + Real.log 2 := by simp
      _ ≤ 36 + Real.log 2 + L + |Real.log z.im| := by linarith
  · -- the circle reaches height `< r`: use the layer-cake bound at scale `r`
    set g : ℂ → ℝ := fun u => max (Real.log (r / |u.im|)) 0 with hg
    have hgm : Measurable g :=
      (Real.measurable_log.comp (measurable_const.div
        (continuous_abs.measurable.comp Complex.measurable_im))).max measurable_const
    have hg0 : ∀ u, 0 ≤ g u := fun u => le_max_right _ _
    have hgl := TwoPoint.lintegral_logRatio_le z hr hr
    rw [div_self hr.ne', Real.sqrt_one, mul_one] at hgl
    have hgi : Integrable g (foldedCircle z r) :=
      ⟨hgm.aestronglyMeasurable, by
        rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)]
        exact lt_of_le_of_lt hgl ENNReal.ofReal_lt_top⟩
    have hgI : ∫ u, g u ∂foldedCircle z r ≤ 36 := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hgl
    have hlogr : -Real.log r ≤ Real.log 2 + |Real.log z.im| := by
      have := Real.log_le_log (by positivity) hrz.le
      rw [Real.log_div hz0.ne' two_ne_zero] at this
      linarith [neg_abs_le (Real.log z.im)]
    have hlr : 0 ≤ -Real.log r := by linarith [Real.log_nonpos hr.le hr1]
    have hpt : ∀ᵐ u ∂foldedCircle z r, |Real.log u.im| ≤ g u + (-Real.log r) + L := by
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H z hr,
        TwoPoint.foldedCircle_ae_norm_le z hr.le] with u huH hun
      have hu0 : 0 < u.im := huH
      rcases le_total u.im 1 with h1 | h1
      · rw [abs_of_nonpos (Real.log_nonpos hu0.le h1)]
        have : Real.log (r / |u.im|) = Real.log r - Real.log u.im := by
          rw [abs_of_pos hu0, Real.log_div hr.ne' hu0.ne']
        have := le_max_left (Real.log (r / |u.im|)) 0
        simp only [hg]
        linarith
      · rw [abs_of_nonneg (Real.log_nonneg h1)]
        have hle : u.im ≤ R + 1 := (Complex.im_le_norm u).trans (by linarith)
        have := Real.log_le_log hu0 hle
        have := le_max_left (Real.log (R + 1)) 0
        have := le_max_right (Real.log (r / |u.im|)) 0
        simp only [hg]
        linarith
    calc ∫ u, |Real.log u.im| ∂foldedCircle z r
        ≤ ∫ u, (g u + (-Real.log r) + L) ∂foldedCircle z r :=
          integral_mono_ae hint ((hgi.add (integrable_const _)).add (integrable_const _)) hpt
      _ = ∫ u, g u ∂foldedCircle z r + (-Real.log r) + L := by
          have j : Integrable (fun u => g u + (-Real.log r)) (foldedCircle z r) :=
            hgi.add (integrable_const _)
          rw [integral_add j (integrable_const _), integral_add hgi (integrable_const _)]
          simp
      _ ≤ 36 + Real.log 2 + L + |Real.log z.im| := by linarith

end CoordReg
end QuantumZipper
