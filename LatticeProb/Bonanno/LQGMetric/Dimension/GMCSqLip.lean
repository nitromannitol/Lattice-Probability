/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqLip at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqKer

/-!
# Lipschitz bounds for the harmonic part `hS` of the Green function of `𝕍` (P2-GMC, WP-24)

On a compact convex `K ⊆ 𝕍`: `|hS a b − hS a b'| ≤ C ‖b − b'‖` for `a, b, b' ∈ K`
(`exists_hS_lip`). Used for the `L²` continuity of circle averages in the centre (the analogue of
QZ `ZeroReg.kernelCov_circle_diff_le` for `ℍ`). Own elementary proof: mean value inequality for
`φ'` (mathlib `Convex.norm_image_sub_le_of_norm_deriv_le`), the integral form `sqQuot` of the
difference quotient, and `|log a − log b| ≤ |a − b|/m` on `[m, ∞)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal ComplexConjugate

namespace LQGMetric

variable {K : Set ℂ}

lemma dslope_sqM_eq {a y : ℂ} (ha : a ∈ openSquare) (hy : y ∈ openSquare) :
    dslope sqM a y = sqQuot y a := by
  by_cases h : y = a
  · subst h; rw [dslope_same, deriv_sqM hy, sqQuot_self hy]
  · rw [dslope_of_ne _ h, slope_def_field, sqM_eq hy, sqM_eq ha, ← sqQuot_mul hy ha,
      mul_div_cancel_left₀ _ (sub_ne_zero.2 h)]

lemma abs_log_sub_log_le {u v m : ℝ} (hm : 0 < m) (hu : m ≤ u) (hv : m ≤ v) :
    |Real.log u - Real.log v| ≤ |u - v| / m := by
  have hu0 : 0 < u := hm.trans_le hu
  have hv0 : 0 < v := hm.trans_le hv
  have h1 : Real.log u - Real.log v ≤ (u - v) / v := by
    rw [← Real.log_div hu0.ne' hv0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
    rw [sub_div, div_self hv0.ne']; exact this
  have h2 : Real.log v - Real.log u ≤ (v - u) / u := by
    rw [← Real.log_div hv0.ne' hu0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
    rw [sub_div, div_self hu0.ne']; exact this
  rw [abs_le]
  constructor
  · have : (v - u) / u ≤ |u - v| / m := by
      rw [abs_sub_comm]
      calc (v - u) / u ≤ |v - u| / u := div_le_div_of_nonneg_right (le_abs_self _) hu0.le
        _ ≤ |v - u| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hu
    linarith
  · calc Real.log u - Real.log v ≤ (u - v) / v := h1
      _ ≤ |u - v| / v := div_le_div_of_nonneg_right (le_abs_self _) hv0.le
      _ ≤ |u - v| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hv

/-- `‖log‖u‖ − log‖v‖‖ ≤ ‖u − v‖/m` for `‖u‖, ‖v‖ ≥ m` -/
lemma abs_log_norm_sub_le {u v : ℂ} {m : ℝ} (hm : 0 < m) (hu : m ≤ ‖u‖) (hv : m ≤ ‖v‖) :
    |Real.log ‖u‖ - Real.log ‖v‖| ≤ ‖u - v‖ / m :=
  (abs_log_sub_log_le hm hu hv).trans
    (div_le_div_of_nonneg_right (abs_norm_sub_norm_le u v) hm.le)

section Bounds

variable (hKU : K ⊆ openSquare) (hKc : Convex ℝ K) (hKk : IsCompact K)
include hKU hKc hKk

lemma exists_sqQuot_bounds :
    ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ K, ∀ y ∈ K, m ≤ ‖sqQuot x y‖ ∧ ‖sqQuot x y‖ ≤ M := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, one_pos, fun x hx => hx.elim⟩
  have hc := (continuousOn_sqQuot hKU hKc hKk).norm
  obtain ⟨p₀, hp₀, hmin⟩ := (hKk.prod hKk).exists_isMinOn (hne.prod hne) hc
  obtain ⟨p₁, -, hmax⟩ := (hKk.prod hKk).exists_isMaxOn (hne.prod hne) hc
  refine ⟨‖sqQuot p₀.1 p₀.2‖, ‖sqQuot p₁.1 p₁.2‖,
    norm_pos_iff.mpr (sqQuot_ne_zero (hKU hp₀.1) (hKU hp₀.2)), fun x hx y hy => ⟨?_, ?_⟩⟩
  · exact hmin (show (x, y) ∈ K ×ˢ K from ⟨hx, hy⟩)
  · exact hmax (show (x, y) ∈ K ×ˢ K from ⟨hx, hy⟩)

lemma exists_deriv_lip :
    ∃ M : ℝ, ∀ a ∈ K, ∀ b ∈ K, ‖deriv sqMap a - deriv sqMap b‖ ≤ M * ‖a - b‖ := by
  have hA := analyticOnNhd_sqMap.deriv
  obtain ⟨M, hM⟩ := hKk.exists_bound_of_continuousOn (hA.deriv.continuousOn.mono hKU)
  refine ⟨M, fun a ha b hb => ?_⟩
  exact hKc.norm_image_sub_le_of_norm_deriv_le (fun x hx => (hA x (hKU hx)).differentiableAt)
    (fun x hx => hM x hx) hb ha

lemma exists_sqQuot_lip :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ K, ∀ b ∈ K, ∀ b' ∈ K, ‖sqQuot b a - sqQuot b' a‖ ≤ M * ‖b - b'‖ := by
  obtain ⟨M, hM⟩ := exists_deriv_lip hKU hKc hKk
  refine ⟨max M 0, le_max_right _ _, fun a ha b hb b' hb' => ?_⟩
  have hseg : ∀ c ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, a + t • (c - a) ∈ K := fun c hc t ht => by
    have := hKc ha hc (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1 (by ring)
    convert this using 1; simp only [Complex.real_smul]; push_cast; ring
  have hcont : ∀ c ∈ K, ContinuousOn (fun t : ℝ => deriv sqMap (a + t • (c - a))) (uIcc 0 1) :=
    fun c hc => (continuousOn_deriv_sqMap.mono hKU).comp (by fun_prop) fun t ht =>
      hseg c hc t (by rwa [uIcc_of_le zero_le_one] at ht)
  unfold sqQuot
  rw [← intervalIntegral.integral_sub ((hcont b hb).intervalIntegrable)
    ((hcont b' hb').intervalIntegrable)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := max M 0 * ‖b - b'‖)
    fun t ht => ?_).trans_eq
    (by simp)
  rw [uIoc_of_le zero_le_one] at ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  refine (hM _ (hseg b hb t ht') _ (hseg b' hb' t ht')).trans ?_
  have : ‖a + t • (b - a) - (a + t • (b' - a))‖ = t * ‖b - b'‖ := by
    rw [show a + t • (b - a) - (a + t • (b' - a)) = t • (b - b') by
      simp only [smul_sub]; ring, norm_smul, Real.norm_of_nonneg ht'.1]
  rw [this]
  calc M * (t * ‖b - b'‖) ≤ max M 0 * (t * ‖b - b'‖) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity [ht'.1])
    _ ≤ max M 0 * ‖b - b'‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
        exact mul_le_of_le_one_left (norm_nonneg _) ht'.2

/-- **Lipschitz bound for `hS` in the second variable**, uniform in the first, on `K` -/
theorem exists_hS_lip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ b ∈ K, ∀ b' ∈ K, |hS a b - hS a b'| ≤ C * ‖b - b'‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, fun x hx => hx.elim⟩
  obtain ⟨m, M, hm, hmM⟩ := exists_sqQuot_bounds hKU hKc hKk
  obtain ⟨M₂, hM₂, hlip⟩ := exists_sqQuot_lip hKU hKc hKk
  -- lower bound on `Im sqM` over `K`
  have hc : ContinuousOn (fun y => (sqM y).im) K :=
    Complex.continuous_im.comp_continuousOn (differentiableOn_sqM.continuousOn.mono hKU)
  obtain ⟨y₀, hy₀, hmin⟩ := hKk.exists_isMinOn hne hc
  set m₁ := (sqM y₀).im
  have hm₁ : 0 < m₁ := sqM_mem_H (hKU hy₀)
  have hlow : ∀ a ∈ K, ∀ y ∈ K, m₁ ≤ ‖sqM y - conj (sqM a)‖ := fun a ha y hy => by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add]
    have h1 : m₁ ≤ (sqM y).im := hmin hy
    have h2 : 0 < (sqM a).im := sqM_mem_H (hKU ha)
    rw [abs_of_pos (by linarith)]; linarith
  refine ⟨max M 0 / m₁ + M₂ / m, by positivity, fun a ha b hb b' hb' => ?_⟩
  rw [hS_eq, hS_eq]
  have e1 := abs_log_norm_sub_le hm₁ (hlow a ha b hb) (hlow a ha b' hb')
  have e2 := abs_log_norm_sub_le hm (hmM b hb a ha).1 (hmM b' hb' a ha).1
  rw [dslope_sqM_eq (hKU ha) (hKU hb), dslope_sqM_eq (hKU ha) (hKU hb')]
  have n1 : ‖sqM b - conj (sqM a) - (sqM b' - conj (sqM a))‖ ≤ max M 0 * ‖b - b'‖ := by
    rw [sub_sub_sub_cancel_right, sqM_eq (hKU hb), sqM_eq (hKU hb'),
      ← sqQuot_mul (hKU hb) (hKU hb'), norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hmM b hb b' hb').2.trans (le_max_left _ _))
      (norm_nonneg _)
  have n2 := hlip a ha b hb b' hb'
  calc |Real.log ‖sqM b - conj (sqM a)‖ - Real.log ‖sqQuot b a‖ -
        (Real.log ‖sqM b' - conj (sqM a)‖ - Real.log ‖sqQuot b' a‖)|
      ≤ |Real.log ‖sqM b - conj (sqM a)‖ - Real.log ‖sqM b' - conj (sqM a)‖| +
        |Real.log ‖sqQuot b a‖ - Real.log ‖sqQuot b' a‖| := by
        rw [show ∀ p q u v : ℝ, p - q - (u - v) = (p - u) - (q - v) from fun _ _ _ _ => by ring]
        exact abs_sub _ _
    _ ≤ max M 0 * ‖b - b'‖ / m₁ + M₂ * ‖b - b'‖ / m := by
        refine add_le_add (e1.trans ?_) (e2.trans ?_)
        · exact div_le_div_of_nonneg_right n1 hm₁.le
        · exact div_le_div_of_nonneg_right n2 hm.le
    _ = (max M 0 / m₁ + M₂ / m) * ‖b - b'‖ := by ring

end Bounds

end LQGMetric
