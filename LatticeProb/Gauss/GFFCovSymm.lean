import Mathlib
import LatticeProb.Gauss.GFFExistence

/-!
# Symmetry of the whole-plane GFF covariance (`LatticeProb.Gauss.WholePlaneCovSymmStmt`)

`wholePlaneCovSymm_proved : WholePlaneCovSymmStmt` states that the covariance `wholePlaneGFFCov o o'` of two
admissible observables is symmetric. The kernel is `wholePlaneCov x y = log (max(|x|,1) max(|y|,1) / |x - y|)`
the smearing measures are Lebesgue measure against test functions (pairings) and the uniform
probability measures on circles (Duplantier-Sheffield, arXiv:0808.1560, Section 3; Armitage-Gardiner for the
logarithmic potential). The three cases are:

* pairing-pairing (`pp_symm`): Fubini on `ℂ × ℂ`;
* circle-pairing (`cp_symm`): Fubini on `ℝ × ℂ`, the circle parameter running over `(0, 2π]`;
* circle-circle (`cc_symm`): Fubini on `ℝ × ℝ`, using Mathlib's circle averages of `log ‖· - a‖`.

The analytic content is the local integrability of the logarithmic kernel: `|wholePlaneCov x y| ≤ 2 log R +
|log |x - y||` on `closedBall 0 R` (`abs_wholePlaneCov_le`), and the translation-invariant dominating functions
`sectDom`. Credit: `logAbsBall`, `abs_log_le_rpow_neg_half`, `norm_log_norm_le_rpow` and
`integrableOn_log_norm_ball` are adapted from earlier log-potential estimates (not imported).
-/

open MeasureTheory Metric Set Filter Topology
open scoped Real

namespace LatticeProb.Gauss

namespace GFFCovSymm

/-! ### The logarithmic kernel -/

lemma wholePlaneCov_comm' (z w : ℂ) : wholePlaneCov z w = wholePlaneCov w z := by
  unfold wholePlaneCov
  rw [norm_sub_rev z w, mul_comm (max ‖z‖ 1)]

lemma wholePlaneCov_eq_log_sub {x y : ℂ} (h : x ≠ y) :
    wholePlaneCov x y = Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log ‖x - y‖ := by
  have ha : max ‖x‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hb : max ‖y‖ 1 ≠ 0 := (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 h)
  unfold wholePlaneCov
  rw [Real.log_div (mul_ne_zero ha hb) hd, Real.log_mul ha hb]

lemma log_max_norm_nonneg (x : ℂ) : 0 ≤ Real.log (max ‖x‖ 1) :=
  Real.log_nonneg (le_max_right _ _)

lemma log_max_norm_le {R : ℝ} (hR : 1 ≤ R) {x : ℂ} (hx : ‖x‖ ≤ R) :
    Real.log (max ‖x‖ 1) ≤ Real.log R :=
  Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) (max_le hx hR)

/-- Upper bound on `closedBall 0 R` (at `x = y` the junk value of the kernel is `0`). -/
lemma wholePlaneCov_le {R : ℝ} (hR : 1 ≤ R) {x y : ℂ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    wholePlaneCov x y ≤ 2 * Real.log R - Real.log ‖x - y‖ := by
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR
  rcases eq_or_ne x y with rfl | h
  · unfold wholePlaneCov
    simp only [sub_self, norm_zero, div_zero, Real.log_zero, sub_zero]
    linarith
  · rw [wholePlaneCov_eq_log_sub h]
    have h1 := log_max_norm_nonneg x
    have h2 := log_max_norm_nonneg y
    have h3 := log_max_norm_le hR hx
    have h4 := log_max_norm_le hR hy
    linarith

/-- Lower bound on `closedBall 0 R`. -/
lemma neg_log_two_mul_le {R : ℝ} (hR : 1 ≤ R) {x y : ℂ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    -Real.log (2 * R) ≤ wholePlaneCov x y := by
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  rcases eq_or_ne x y with rfl | h
  · unfold wholePlaneCov
    simp only [sub_self, norm_zero, div_zero, Real.log_zero]
    linarith
  · rw [wholePlaneCov_eq_log_sub h]
    have h1 := log_max_norm_nonneg x
    have h2 := log_max_norm_nonneg y
    have ht : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
    have ht2 : ‖x - y‖ ≤ 2 * R := by linarith [norm_sub_le x y]
    have h5 : Real.log ‖x - y‖ ≤ Real.log (2 * R) := Real.log_le_log ht ht2
    linarith

/-- Absolute value on `closedBall 0 R`: the local integrability bound of the logarithmic kernel. -/
lemma abs_wholePlaneCov_le {R : ℝ} (hR : 1 ≤ R) {x y : ℂ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |wholePlaneCov x y| ≤ 2 * Real.log R + |Real.log ‖x - y‖| := by
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR
  rcases eq_or_ne x y with rfl | h
  · unfold wholePlaneCov
    simp only [sub_self, norm_zero, div_zero, Real.log_zero, abs_zero, add_zero]
    linarith
  · rw [wholePlaneCov_eq_log_sub h]
    have h1 := log_max_norm_nonneg x
    have h2 := log_max_norm_nonneg y
    have h3 := log_max_norm_le hR hx
    have h4 := log_max_norm_le hR hy
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (Real.log ‖x - y‖), neg_le_abs (Real.log ‖x - y‖), abs_nonneg (Real.log ‖x - y‖)]

lemma measurable_wholePlaneCov_pair : Measurable (fun p : ℂ × ℂ => wholePlaneCov p.1 p.2) := by
  unfold wholePlaneCov
  fun_prop

lemma measurable_kernel_comp {α : Type*} [MeasurableSpace α] {f g : α → ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun a => wholePlaneCov (f a) (g a)) :=
  measurable_wholePlaneCov_pair.comp (hf.prodMk hg)

/-- The norm of a point of a circle `circleMap c r θ` is at most `‖c‖ + |r|`. -/
lemma norm_circleMap_le' (c : ℂ) (r : ℝ) (θ : ℝ) : ‖circleMap c r θ‖ ≤ ‖c‖ + |r| := by
  unfold circleMap
  calc ‖c + (r : ℂ) * Complex.exp (θ * Complex.I)‖ ≤ ‖c‖ + ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ :=
        norm_add_le _ _
    _ = ‖c‖ + |r| := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-! ### Local integrability of `log` on `ℂ` -/

lemma abs_log_le_rpow_neg_half {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    |Real.log r| ≤ 2 * r ^ (-(1 / 2 : ℝ)) := by
  rw [abs_of_nonpos (Real.log_nonpos hr0.le hr1)]
  have h := Real.log_le_rpow_div (x := r⁻¹) (ε := 1 / 2) (by positivity) (by norm_num)
  rw [Real.log_inv, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le] at h
  linarith

lemma norm_log_norm_le_rpow {T : ℝ} (hT : 0 < T) {x : ℂ} (hx : ‖x‖ < T) :
    ‖Real.log ‖x‖‖ ≤ (2 + |Real.log T| * T ^ (1 / 2 : ℝ)) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h0 | hpos
  · rw [← h0]; simp
  set r := ‖x‖ with hr_def
  have hrpow : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hpos.le _
  have hX : 0 ≤ |Real.log T| * T ^ (1 / 2 : ℝ) := by positivity
  have hsplit : (2 + |Real.log T| * T ^ (1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ)) =
      2 * r ^ (-(1 / 2 : ℝ)) + |Real.log T| * T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by ring
  rw [Real.norm_eq_abs, hsplit]
  rcases le_total r 1 with h1 | h1
  · have := abs_log_le_rpow_neg_half hpos h1
    nlinarith [mul_nonneg hX hrpow]
  · have hlog : 0 ≤ Real.log r := Real.log_nonneg h1
    rw [abs_of_nonneg hlog]
    have hrT : r ≤ T := hx.le
    have hsq : r ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hpos.le hrT (by norm_num)
    have hone : 1 ≤ T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hpos _), one_mul]
      exact hsq
    have hlogT : Real.log r ≤ |Real.log T| := le_trans (Real.log_le_log hpos hrT) (le_abs_self _)
    have hmain : |Real.log T| ≤ |Real.log T| * (T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) := by
      have := mul_nonneg (abs_nonneg (Real.log T)) (sub_nonneg.2 hone)
      nlinarith
    have e : |Real.log T| * (T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) =
        |Real.log T| * T ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by ring
    linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hrpow]

/-- `log ‖·‖` is integrable on every ball of `ℂ` centred at `0`. -/
lemma integrableOn_log_norm_ball (T : ℝ) :
    IntegrableOn (fun w : ℂ => Real.log ‖w‖) (ball 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · rw [ball_eq_empty.2 (by linarith : T ≤ 0)]
    exact integrableOn_empty
  · refine integrableOn_ball_of_norm_le_rpow (C := 2 + |Real.log T| * T ^ (1 / 2 : ℝ))
      (α := 1 / 2) ?_ ?_ ?_ ?_
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num
    · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
      exact norm_log_norm_le_rpow hT (mem_ball_zero_iff.1 hx)
    · exact (Measurable.log measurable_norm).aestronglyMeasurable

/-- The logarithmic kernel truncated to a ball: `|log ‖u‖|` on `ball 0 T`, zero outside. -/
noncomputable def logAbsBall (T : ℝ) (u : ℂ) : ℝ :=
  (ball (0 : ℂ) T).indicator (fun u => |Real.log ‖u‖|) u

lemma logAbsBall_nonneg (T : ℝ) (u : ℂ) : 0 ≤ logAbsBall T u :=
  indicator_nonneg (fun _ _ => abs_nonneg _) u

lemma logAbsBall_eq_abs {T : ℝ} {u : ℂ} (hu : ‖u‖ < T) : logAbsBall T u = |Real.log ‖u‖| := by
  unfold logAbsBall
  rw [indicator_of_mem (mem_ball_zero_iff.2 hu)]

lemma integrable_logAbsBall (T : ℝ) : Integrable (logAbsBall T) := by
  unfold logAbsBall
  rw [integrable_indicator_iff measurableSet_ball]
  exact (integrableOn_log_norm_ball T).abs

/-! ### Translation-invariant dominating functions -/

/-- `x ↦ 2 log R · 1_{closedBall 0 R}(x) + |log ‖x - w‖|`, a dominating function of the kernel in its first
argument for `‖w‖ ≤ R`, `R ≥ 1`. -/
noncomputable def sectDom (R : ℝ) (w x : ℂ) : ℝ :=
  (closedBall (0 : ℂ) R).indicator (fun _ => 2 * Real.log R) x + logAbsBall (2 * R + 1) (x - w)

lemma sectDom_nonneg {R : ℝ} (hR : 1 ≤ R) (w x : ℂ) : 0 ≤ sectDom R w x := by
  unfold sectDom
  refine add_nonneg (indicator_nonneg (fun _ _ => ?_) _) (logAbsBall_nonneg _ _)
  have := Real.log_nonneg hR
  linarith

lemma integrable_indicator_const_closedBall (R c : ℝ) :
    Integrable ((closedBall (0 : ℂ) R).indicator (fun _ => c)) := by
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact integrableOn_const (measure_closedBall_lt_top).ne

lemma integrable_sectDom (R : ℝ) (w : ℂ) : Integrable (sectDom R w) := by
  unfold sectDom
  exact (integrable_indicator_const_closedBall R _).add ((integrable_logAbsBall _).comp_sub_right w)

/-- The mass of the dominating function does not depend on the centre. -/
lemma integral_sectDom (R : ℝ) (w : ℂ) : ∫ x, sectDom R w x = ∫ x, sectDom R 0 x := by
  simp only [sectDom, sub_zero]
  rw [integral_add (integrable_indicator_const_closedBall R _) ((integrable_logAbsBall _).comp_sub_right w),
    integral_add (integrable_indicator_const_closedBall R _) (integrable_logAbsBall _),
    integral_sub_right_eq_self (logAbsBall (2 * R + 1)) w]

/-- Pointwise domination of `ψ(y) K(x,y)` by `Cψ · sectDom R x y`. -/
lemma norm_mul_wholePlaneCov_le {R : ℝ} (hR : 1 ≤ R) {ψ : ℂ → ℝ} {Cψ : ℝ} (hCψ : ∀ y, ‖ψ y‖ ≤ Cψ)
    (hψR : ∀ y, ψ y ≠ 0 → ‖y‖ ≤ R) {x : ℂ} (hx : ‖x‖ ≤ R) (y : ℂ) :
    ‖ψ y * wholePlaneCov x y‖ ≤ Cψ * sectDom R x y := by
  have hC : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0)
  rw [norm_mul]
  by_cases hy : ‖y‖ ≤ R
  · have hlt : ‖y - x‖ < 2 * R + 1 := by linarith [norm_sub_le y x]
    have h1 := abs_wholePlaneCov_le hR hx hy
    rw [norm_sub_rev x y] at h1
    have hK : ‖wholePlaneCov x y‖ ≤ 2 * Real.log R + logAbsBall (2 * R + 1) (y - x) := by
      rw [Real.norm_eq_abs, logAbsBall_eq_abs hlt]
      exact h1
    have hind : (closedBall (0 : ℂ) R).indicator (fun _ => 2 * Real.log R) y = 2 * Real.log R :=
      indicator_of_mem (mem_closedBall_zero_iff.2 hy) _
    unfold sectDom
    rw [hind]
    exact mul_le_mul (hCψ y) hK (norm_nonneg _) hC
  · have hψ0 : ψ y = 0 := by
      by_contra h
      exact hy (hψR y h)
    rw [hψ0, norm_zero, zero_mul]
    exact mul_nonneg hC (sectDom_nonneg hR x y)

/-! ### Generic Fubini integrability and test-function facts -/

/-- Integrability on a product from the sections: a.e. integrable sections, and the section integrals of the norm
dominated by an integrable function of the first variable. -/
lemma integrable_prod_of_sections {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f : α × β → ℝ} (hf : Measurable f)
    {G : α → ℝ} (hG : Integrable G μ) (h1 : ∀ᵐ a ∂μ, Integrable (fun b => f (a, b)) ν)
    (h2 : ∀ a, ∫ b, ‖f (a, b)‖ ∂ν ≤ G a) : Integrable f (μ.prod ν) := by
  refine (integrable_prod_iff hf.aestronglyMeasurable).2 ⟨h1, ?_⟩
  refine hG.mono' (hf.norm.aestronglyMeasurable.integral_prod_right') (ae_of_all _ fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact h2 a

lemma exists_radius {f : ℂ → ℝ} (hf : HasCompactSupport f) : ∃ R : ℝ, ∀ x, f x ≠ 0 → ‖x‖ ≤ R := by
  obtain ⟨C, hC⟩ := hf.isCompact.isBounded.exists_norm_le
  exact ⟨C, fun x hx => hC x (subset_tsupport f (Function.mem_support.2 hx))⟩

lemma exists_bound {f : ℂ → ℝ} (hf : IsTestFunction univ f) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C :=
  hf.1.continuous.bounded_above_of_compact_support hf.2.1

lemma integrable_of_test {f : ℂ → ℝ} (hf : IsTestFunction univ f) : Integrable f :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2.1

/-! ### Circle averages of the logarithm -/

/-- Integrability of `ϑ ↦ log ‖circleMap w s ϑ - x‖` on `(0, 2π]` (Mathlib, circle integrability of `log ‖· - a‖`). -/
lemma integrable_log_circle (w x : ℂ) (s : ℝ) :
    Integrable (fun ϑ : ℝ => Real.log ‖circleMap w s ϑ - x‖) (volume.restrict (Ioc 0 (2 * π))) := by
  have h := circleIntegrable_log_norm_sub_const (a := x) (c := w) s
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 h

/-- The circle average of `log ‖· - x‖` over `∂B_s(w)` is at least `log s` (Mathlib's explicit formula). -/
lemma two_pi_mul_log_le_integral_log_circle (w x : ℂ) {s : ℝ} (hs : 0 < s) :
    2 * π * Real.log s ≤ ∫ ϑ in Ioc 0 (2 * π), Real.log ‖circleMap w s ϑ - x‖ := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := x) (c := w) (R := s) hs.ne'
  have hpos : 0 ≤ Real.posLog (s⁻¹ * ‖w - x‖) := Real.posLog_nonneg
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity), smul_eq_mul] at h
  calc 2 * π * Real.log s ≤ 2 * π * (Real.log s + Real.posLog (s⁻¹ * ‖w - x‖)) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 * π * ((2 * π)⁻¹ * ∫ ϑ in Ioc 0 (2 * π), Real.log ‖circleMap w s ϑ - x‖) := by rw [h]
    _ = ∫ ϑ in Ioc 0 (2 * π), Real.log ‖circleMap w s ϑ - x‖ := by
        field_simp

lemma volume_restrict_Ioc_univ_real : (volume.restrict (Ioc 0 (2 * π))).real univ = 2 * π := by
  rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-! ### Pairing-pairing -/

lemma pp_symm {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ) :
    wholePlaneGFFCov (.pairing φ) (.pairing ψ) = wholePlaneGFFCov (.pairing ψ) (.pairing φ) := by
  obtain ⟨R0, hR0⟩ := exists_radius hφ.2.1
  obtain ⟨R1, hR1⟩ := exists_radius hψ.2.1
  obtain ⟨Cψ, hCψ⟩ := exists_bound hψ
  set R : ℝ := max 1 (max R0 R1) with hRdef
  have hR : 1 ≤ R := le_max_left _ _
  have hR0R : R0 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR1R : R1 ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hφR : ∀ x, φ x ≠ 0 → ‖x‖ ≤ R := fun x hx => (hR0 x hx).trans hR0R
  have hψR : ∀ y, ψ y ≠ 0 → ‖y‖ ≤ R := fun y hy => (hR1 y hy).trans hR1R
  have hφm : Measurable φ := hφ.1.continuous.measurable
  have hψm : Measurable ψ := hψ.1.continuous.measurable
  have hFm : Measurable (fun p : ℂ × ℂ => φ p.1 * (ψ p.2 * wholePlaneCov p.1 p.2)) :=
    (hφm.comp measurable_fst).mul ((hψm.comp measurable_snd).mul measurable_wholePlaneCov_pair)
  have hbound : ∀ x y : ℂ, ‖φ x * (ψ y * wholePlaneCov x y)‖ ≤ (|φ x| * Cψ) * sectDom R x y := by
    intro x y
    by_cases hφx : φ x = 0
    · simp [hφx]
    · rw [norm_mul, Real.norm_eq_abs (φ x)]
      calc |φ x| * ‖ψ y * wholePlaneCov x y‖ ≤ |φ x| * (Cψ * sectDom R x y) :=
            mul_le_mul_of_nonneg_left (norm_mul_wholePlaneCov_le hR hCψ hψR (hφR x hφx) y) (abs_nonneg _)
        _ = (|φ x| * Cψ) * sectDom R x y := by ring
  have hsec : ∀ x, Integrable (fun y => φ x * (ψ y * wholePlaneCov x y)) volume := by
    intro x
    refine Integrable.mono' ((integrable_sectDom R x).const_mul (|φ x| * Cψ)) ?_
      (ae_of_all _ fun y => hbound x y)
    exact (hFm.comp (measurable_prodMk_left (x := x))).aestronglyMeasurable
  have hG : Integrable (fun x => |φ x| * Cψ * ∫ y, sectDom R 0 y) volume :=
    (((integrable_of_test hφ).abs).mul_const Cψ).mul_const _
  have hF : Integrable (Function.uncurry fun x y => φ x * (ψ y * wholePlaneCov x y)) (volume.prod volume) := by
    refine integrable_prod_of_sections (μ := volume) (ν := volume) hFm hG (ae_of_all _ hsec) fun x => ?_
    calc ∫ y, ‖φ x * (ψ y * wholePlaneCov x y)‖ ≤ ∫ y, (|φ x| * Cψ) * sectDom R x y :=
          integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
            ((integrable_sectDom R x).const_mul _) (ae_of_all _ fun y => hbound x y)
      _ = |φ x| * Cψ * ∫ y, sectDom R 0 y := by
          rw [integral_const_mul, integral_sectDom]
  have key : ∀ t x : ℂ, φ x * (ψ t * wholePlaneCov x t) = ψ t * (φ x * wholePlaneCov t x) := by
    intro t x
    rw [wholePlaneCov_comm' x t]
    ring
  show (∫ x, φ x * ∫ y, ψ y * wholePlaneCov x y) = ∫ x, ψ x * ∫ y, φ y * wholePlaneCov x y
  calc (∫ x, φ x * ∫ y, ψ y * wholePlaneCov x y)
      = ∫ x, ∫ y, φ x * (ψ y * wholePlaneCov x y) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ y, ∫ x, φ x * (ψ y * wholePlaneCov x y) := integral_integral_swap hF
    _ = ∫ x, ψ x * ∫ y, φ y * wholePlaneCov x y := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only [key t, integral_const_mul]

/-! ### Circle-pairing -/

instance isFiniteMeasure_restrict_Ioc_two_pi :
    IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩

lemma cp_symm {r : ℝ} {z : ℂ} {ψ : ℂ → ℝ} (hr : 0 < r) (hψ : IsTestFunction univ ψ) :
    wholePlaneGFFCov (.circle r z) (.pairing ψ) = wholePlaneGFFCov (.pairing ψ) (.circle r z) := by
  obtain ⟨R0, hR0⟩ := exists_radius hψ.2.1
  obtain ⟨Cψ, hCψ⟩ := exists_bound hψ
  set R : ℝ := max 1 (max R0 (‖z‖ + r)) with hRdef
  have hR : 1 ≤ R := le_max_left _ _
  have hR0R : R0 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hzR : ‖z‖ + r ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have hψR : ∀ y, ψ y ≠ 0 → ‖y‖ ≤ R := fun y hy => (hR0 y hy).trans hR0R
  have hcR : ∀ θ : ℝ, ‖circleMap z r θ‖ ≤ R := fun θ =>
    (norm_circleMap_le' z r θ).trans (by rw [abs_of_pos hr]; exact hzR)
  have hψm : Measurable ψ := hψ.1.continuous.measurable
  have hFm : Measurable (fun p : ℝ × ℂ => ψ p.2 * wholePlaneCov (circleMap z r p.1) p.2) :=
    (hψm.comp measurable_snd).mul
      (measurable_kernel_comp ((continuous_circleMap z r).measurable.comp measurable_fst) measurable_snd)
  have hF : Integrable (fun p : ℝ × ℂ => ψ p.2 * wholePlaneCov (circleMap z r p.1) p.2)
      ((volume.restrict (Ioc 0 (2 * π))).prod volume) := by
    refine integrable_prod_of_sections (μ := volume.restrict (Ioc 0 (2 * π))) (ν := volume) hFm
      (G := fun _ => Cψ * ∫ y, sectDom R 0 y) (integrable_const _) (ae_of_all _ fun θ => ?_) (fun θ => ?_)
    · refine Integrable.mono' ((integrable_sectDom R (circleMap z r θ)).const_mul Cψ) ?_
        (ae_of_all _ fun y => norm_mul_wholePlaneCov_le hR hCψ hψR (hcR θ) y)
      exact (hFm.comp (measurable_prodMk_left (x := θ))).aestronglyMeasurable
    · calc ∫ y, ‖ψ y * wholePlaneCov (circleMap z r θ) y‖
          ≤ ∫ y, Cψ * sectDom R (circleMap z r θ) y :=
            integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
              ((integrable_sectDom R _).const_mul _)
              (ae_of_all _ fun y => norm_mul_wholePlaneCov_le hR hCψ hψR (hcR θ) y)
        _ = Cψ * ∫ y, sectDom R 0 y := by rw [integral_const_mul, integral_sectDom]
  have hswap := integral_integral_swap (μ := volume.restrict (Ioc 0 (2 * π))) (ν := volume)
    (f := fun θ y => ψ y * wholePlaneCov (circleMap z r θ) y) hF
  have hc : ∀ (x : ℂ) (θ : ℝ), wholePlaneCov (circleMap z r θ) x = wholePlaneCov x (circleMap z r θ) :=
    fun x θ => wholePlaneCov_comm' _ _
  have hRHS : ∀ x : ℂ, ψ x * ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), wholePlaneCov x (circleMap z r θ)) =
      (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ψ x * wholePlaneCov (circleMap z r θ) x := by
    intro x
    simp only [hc x, integral_const_mul]
    ring
  show Real.circleAverage (fun x => ∫ y, ψ y * wholePlaneCov x y) z r =
    ∫ x, ψ x * Real.circleAverage (fun y => wholePlaneCov x y) z r
  simp only [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  have hsum : ∫ x, ψ x * ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), wholePlaneCov x (circleMap z r θ)) =
      (2 * π)⁻¹ * ∫ x, ∫ θ in Ioc 0 (2 * π), ψ x * wholePlaneCov (circleMap z r θ) x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hRHS)
  rw [hsum, ← hswap]

/-! ### Circle-circle -/

lemma cc_symm {r s : ℝ} {z w : ℂ} (hr : 0 < r) (hs : 0 < s) :
    wholePlaneGFFCov (.circle r z) (.circle s w) = wholePlaneGFFCov (.circle s w) (.circle r z) := by
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  set R : ℝ := ‖z‖ + r + ‖w‖ + s + 1 with hRdef
  have hR : 1 ≤ R := by linarith
  have hc1 : ∀ θ : ℝ, ‖circleMap z r θ‖ ≤ R := fun θ =>
    (norm_circleMap_le' z r θ).trans (by rw [abs_of_pos hr]; linarith)
  have hc2 : ∀ ϑ : ℝ, ‖circleMap w s ϑ‖ ≤ R := fun ϑ =>
    (norm_circleMap_le' w s ϑ).trans (by rw [abs_of_pos hs]; linarith)
  have hHm : Measurable (fun p : ℝ × ℝ => wholePlaneCov (circleMap z r p.1) (circleMap w s p.2)) :=
    measurable_kernel_comp ((continuous_circleMap z r).measurable.comp measurable_fst)
      ((continuous_circleMap w s).measurable.comp measurable_snd)
  have hsec : ∀ θ : ℝ, Integrable (fun ϑ : ℝ => wholePlaneCov (circleMap z r θ) (circleMap w s ϑ))
      (volume.restrict (Ioc 0 (2 * π))) := by
    intro θ
    refine Integrable.mono'
      ((integrable_const (2 * Real.log R)).add (integrable_log_circle w (circleMap z r θ) s).abs) ?_
      (ae_of_all _ fun ϑ => ?_)
    · exact (hHm.comp (measurable_prodMk_left (x := θ))).aestronglyMeasurable
    · have h := abs_wholePlaneCov_le hR (hc1 θ) (hc2 ϑ)
      rw [norm_sub_rev (circleMap z r θ) (circleMap w s ϑ)] at h
      rw [Real.norm_eq_abs]
      exact h
  have hbd : ∀ θ : ℝ, ∫ ϑ, ‖wholePlaneCov (circleMap z r θ) (circleMap w s ϑ)‖
      ∂(volume.restrict (Ioc 0 (2 * π))) ≤
      4 * π * Real.log R - 2 * π * Real.log s + 4 * π * Real.log (2 * R) := by
    intro θ
    have hlog2 : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
    have hpt : ∀ ϑ : ℝ, ‖wholePlaneCov (circleMap z r θ) (circleMap w s ϑ)‖ ≤
        wholePlaneCov (circleMap z r θ) (circleMap w s ϑ) + 2 * Real.log (2 * R) := by
      intro ϑ
      have hlow := neg_log_two_mul_le hR (hc1 θ) (hc2 ϑ)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hup : ∀ ϑ : ℝ, wholePlaneCov (circleMap z r θ) (circleMap w s ϑ) ≤
        2 * Real.log R - Real.log ‖circleMap w s ϑ - circleMap z r θ‖ := by
      intro ϑ
      have h := wholePlaneCov_le hR (hc1 θ) (hc2 ϑ)
      rw [norm_sub_rev (circleMap z r θ) (circleMap w s ϑ)] at h
      exact h
    have hLint := integrable_log_circle w (circleMap z r θ) s
    have hL2 := two_pi_mul_log_le_integral_log_circle w (circleMap z r θ) hs
    have hvol := volume_restrict_Ioc_univ_real
    calc ∫ ϑ, ‖wholePlaneCov (circleMap z r θ) (circleMap w s ϑ)‖ ∂(volume.restrict (Ioc 0 (2 * π)))
        ≤ ∫ ϑ, (wholePlaneCov (circleMap z r θ) (circleMap w s ϑ) + 2 * Real.log (2 * R))
            ∂(volume.restrict (Ioc 0 (2 * π))) :=
          integral_mono_of_nonneg (ae_of_all _ fun ϑ => norm_nonneg _)
            ((hsec θ).add (integrable_const _)) (ae_of_all _ hpt)
      _ = (∫ ϑ, wholePlaneCov (circleMap z r θ) (circleMap w s ϑ) ∂(volume.restrict (Ioc 0 (2 * π))))
            + 2 * Real.log (2 * R) * (2 * π) := by
          rw [integral_add (hsec θ) (integrable_const _), integral_const, hvol, smul_eq_mul]
          ring
      _ ≤ (∫ ϑ, (2 * Real.log R - Real.log ‖circleMap w s ϑ - circleMap z r θ‖)
            ∂(volume.restrict (Ioc 0 (2 * π)))) + 2 * Real.log (2 * R) * (2 * π) := by
          have h3 : ∫ ϑ, wholePlaneCov (circleMap z r θ) (circleMap w s ϑ)
              ∂(volume.restrict (Ioc 0 (2 * π))) ≤
              ∫ ϑ, (2 * Real.log R - Real.log ‖circleMap w s ϑ - circleMap z r θ‖)
                ∂(volume.restrict (Ioc 0 (2 * π))) :=
            integral_mono (hsec θ) ((integrable_const (2 * Real.log R)).sub hLint) (fun ϑ => hup ϑ)
          linarith
      _ = 2 * Real.log R * (2 * π)
            - (∫ ϑ, Real.log ‖circleMap w s ϑ - circleMap z r θ‖ ∂(volume.restrict (Ioc 0 (2 * π))))
            + 2 * Real.log (2 * R) * (2 * π) := by
          rw [integral_sub (integrable_const _) hLint, integral_const, hvol, smul_eq_mul]
          ring
      _ ≤ 4 * π * Real.log R - 2 * π * Real.log s + 4 * π * Real.log (2 * R) := by
          linarith [hL2]
  have hHint : Integrable (fun p : ℝ × ℝ => wholePlaneCov (circleMap z r p.1) (circleMap w s p.2))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))) :=
    integrable_prod_of_sections (μ := volume.restrict (Ioc 0 (2 * π)))
      (ν := volume.restrict (Ioc 0 (2 * π))) hHm
      (G := fun _ => 4 * π * Real.log R - 2 * π * Real.log s + 4 * π * Real.log (2 * R))
      (integrable_const _) (ae_of_all _ hsec) hbd
  have hLHS : wholePlaneGFFCov (.circle r z) (.circle s w) =
      (2 * π)⁻¹ * ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ∫ ϑ in Ioc 0 (2 * π),
        wholePlaneCov (circleMap z r θ) (circleMap w s ϑ)) := by
    show Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) w s) z r = _
    simp only [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le,
      integral_const_mul]
  have hcomm : ∀ ϑ θ : ℝ, wholePlaneCov (circleMap w s ϑ) (circleMap z r θ) =
      wholePlaneCov (circleMap z r θ) (circleMap w s ϑ) := fun ϑ θ => wholePlaneCov_comm' _ _
  have hRHS : wholePlaneGFFCov (.circle s w) (.circle r z) =
      (2 * π)⁻¹ * ((2 * π)⁻¹ * ∫ ϑ in Ioc 0 (2 * π), ∫ θ in Ioc 0 (2 * π),
        wholePlaneCov (circleMap z r θ) (circleMap w s ϑ)) := by
    show Real.circleAverage (fun y => Real.circleAverage (fun x => wholePlaneCov y x) z r) w s = _
    simp only [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le,
      integral_const_mul, hcomm]
  rw [hLHS, hRHS, integral_integral_swap (f := fun θ ϑ => wholePlaneCov (circleMap z r θ) (circleMap w s ϑ))
    hHint]

end GFFCovSymm

/-- The whole-plane covariance kernel is symmetric on admissible observables: `WholePlaneCovSymmStmt` holds
(Fubini on pairings and circle averages; `GFFCovSymm.pp_symm`, `cp_symm`, `cc_symm`). -/
theorem wholePlaneCovSymm_proved : WholePlaneCovSymmStmt := by
  rintro ⟨o, ho⟩ ⟨o', ho'⟩
  cases o with
  | pairing φ =>
    cases o' with
    | pairing ψ => exact GFFCovSymm.pp_symm ho ho'
    | circle s w => exact (GFFCovSymm.cp_symm ho' ho).symm
  | circle r z =>
    cases o' with
    | pairing ψ => exact GFFCovSymm.cp_symm ho ho'
    | circle s w => exact GFFCovSymm.cc_symm ho ho'

/-- `exists_isWholePlaneGFF` with the symmetry input discharged by `wholePlaneCovSymm_proved`: the only named
input left is the positive semidefiniteness `WholePlaneCovPSDStmt` (B2). -/
theorem exists_isWholePlaneGFF_of_psd (hB2 : WholePlaneCovPSDStmt)
    (hvarK : ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : ℝ × (Fin 2 → ℝ), a ≤ p.1 → a ≤ q.1 →
      wholePlaneGFFCov (ptObs p) (ptObs p) + wholePlaneGFFCov (ptObs q) (ptObs q)
        - 2 * wholePlaneGFFCov (ptObs p) (ptObs q) ≤ C * dist p q) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc :=
  exists_isWholePlaneGFF hB2 wholePlaneCovSymm_proved hvarK

end LatticeProb.Gauss
