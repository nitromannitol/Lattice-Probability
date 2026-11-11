import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.DiscreteSubset

/-!
# Circle integrals of affine maps and of logarithmic singularities

Elementary facts about circles in `ℂ` and about logarithmic kernels, in the form used for the whole-plane
covariance kernel and for the circle averages of the radial processes of a quantum cone (Duplantier-Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Section 3.1; Armitage-Gardiner, *Classical Potential
Theory*, Springer 2001, Section 3.1).

* Affine maps `u ↦ r u + z` with `r > 0` transport circle averages (`circleAverage_affine`) and integrals on `ℂ`
  (`integral_affine_change`, `integral_affine_pullback`).
* The truncated logarithm `log max(‖w‖, 1)` is continuous and equals `log⁺ ‖w‖` (`continuous_log_max_norm`,
  `posLog_norm_eq_log_max`); the codiscrete filter of a set contains the complement of a point
  (`eventually_ne_codiscreteWithin`).
* The logarithmic mean value property on a circle with arbitrary centre (`circleAverage_log_norm_eq`).
* Integrability of logarithmic singularities on circles. The modulus of `circleMap z r ·` is bounded below by
  `|‖z‖ - r|` and above by `‖z‖ + r` (`abs_norm_sub_le_norm_circleMap`, `norm_circleMap_le_add`). For a circle through
  the origin, `‖z‖ = r`, the modulus is `2 r |cos((θ - α)/2)|` (`norm_circleMap_tangent`), and `log |cos|` is interval
  integrable (`intervalIntegrable_log_cos_affine`). Consequently `θ ↦ 1_{‖circleMap z r θ‖ ≤ 1} (-log ‖circleMap z r θ‖)`
  is integrable on `(0, 2π]` (`integrableOn_log_small_circleMap`), with the tangent case isolated in
  `integrableOn_log_small_tangent`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped Real NNReal ENNReal

namespace LatticeProb.CircleLogIntegrals

/-- **Scaling of circle averages.** For `r ∈ ℝ`, `avg_{u ∈ ∂B_s(w)} f (r u + z) = avg_{v ∈ ∂B_{rs}(r w + z)} f v`. -/
theorem circleAverage_affine (f : ℂ → ℝ) (r : ℝ) (z w : ℂ) (s : ℝ) :
    Real.circleAverage (fun u => f (r * u + z)) w s = Real.circleAverage f (r * w + z) (r * s) := by
  unfold Real.circleAverage
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [circleMap]
  congr 1
  push_cast
  ring

/-- **Change of variables on `ℂ`.** For `r > 0`: `∫ u, F u = r² ∫ x, F (r x + z)`. -/
theorem integral_affine_change (F : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ u, F u = r ^ 2 * ∫ x, F ((r : ℂ) * x + z) := by
  have hT : ∫ x : ℂ, F (x + z) = ∫ u, F u := integral_add_right_eq_self F z
  have hS := Measure.integral_comp_smul (volume : Measure ℂ) (fun x : ℂ => F (x + z)) r
  rw [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.2 (sq_nonneg r)), smul_eq_mul] at hS
  simp only [Complex.real_smul] at hS
  rw [hS, ← hT, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul]

/-- **Change of variables for pairings.** For `r > 0`: `∫ y, φ((y - z)/r) F(y) dy = r² ∫ x, φ(x) F(r x + z) dx`. -/
theorem integral_affine_pullback (φ F : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∫ y, φ ((y - z) / (r : ℂ)) * F y = r ^ 2 * ∫ x, φ x * F ((r : ℂ) * x + z) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [integral_affine_change (fun y => φ ((y - z) / (r : ℂ)) * F y) hr z]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_right, mul_div_cancel_left₀ x hr']

/-- `log⁺ ‖x‖ = log max(‖x‖, 1)`. -/
theorem posLog_norm_eq_log_max (x : ℂ) : Real.posLog ‖x‖ = Real.log (max ‖x‖ 1) := by
  rcases le_total ‖x‖ 1 with h | h
  · rw [max_eq_right h, Real.log_one]
    exact max_eq_left (Real.log_nonpos (norm_nonneg x) h)
  · rw [max_eq_left h]
    exact max_eq_right (Real.log_nonneg h)

/-- The logarithmic mean value property on a circle of radius `r > 0` with arbitrary centre `z`:
the circle average of `w ↦ log ‖w - u‖` is `log r + log⁺ (‖z - u‖ / r)` (Mathlib
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). -/
theorem circleAverage_log_norm_eq (z u : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun w => Real.log ‖w - u‖) z r =
      Real.log r + Real.posLog (r⁻¹ * ‖z - u‖) :=
  circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne'

/-- `w ↦ log max(‖w‖, 1)` is continuous. -/
theorem continuous_log_max_norm : Continuous fun w : ℂ => Real.log (max ‖w‖ 1) :=
  (continuous_norm.max continuous_const).log fun _ => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'

/-- The codiscrete filter of any set contains the complement of a point. -/
theorem eventually_ne_codiscreteWithin (S : Set ℂ) (u : ℂ) :
    ∀ᶠ w in codiscreteWithin S, w ≠ u := by
  rw [eventually_codiscreteWithin_iff_forall_eventually_nhdsNE]
  intro x _
  by_cases hxu : x = u
  · subst hxu
    exact eventually_nhdsWithin_of_forall fun y hy _ => hy
  · exact ((eventually_ne_nhds hxu).filter_mono nhdsWithin_le_nhds).mono fun y hy _ => hy

/-- The modulus of a complex number of the form `e^{iα} + e^{iθ}` is `2 |cos((θ - α)/2)|`. -/
lemma norm_exp_add_exp_mul_I (α θ : ℝ) :
    ‖Complex.exp (α * Complex.I) + Complex.exp (θ * Complex.I)‖ = 2 * |Real.cos ((θ - α) / 2)| := by
  have h1 : Complex.exp (α * Complex.I)
      = Complex.exp (((α + θ) / 2 : ℝ) * Complex.I) * Complex.exp (-(((θ - α) / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (θ * Complex.I)
      = Complex.exp (((α + θ) / 2 : ℝ) * Complex.I) * Complex.exp ((((θ - α) / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h3 : Complex.exp (-(((θ - α) / 2 : ℝ) : ℂ) * Complex.I)
      + Complex.exp ((((θ - α) / 2 : ℝ) : ℂ) * Complex.I) = 2 * ((Real.cos ((θ - α) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.two_cos, add_comm]
  rw [h1, h2, ← mul_add, h3, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- On a circle through the origin, `‖z‖ = r`, write `z = r e^{iα}`; then `‖circleMap z r θ‖ = 2 r |cos((θ-α)/2)|`. -/
lemma norm_circleMap_tangent {r : ℝ} (hr : 0 < r) (α θ : ℝ) :
    ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖ = 2 * r * |Real.cos ((θ - α) / 2)| := by
  have hx : circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ
      = (r : ℂ) * (Complex.exp (α * Complex.I) + Complex.exp (θ * Complex.I)) := by
    simp only [circleMap]; ring
  rw [hx, norm_mul, norm_exp_add_exp_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  ring

/-- Reverse triangle inequality on a circle: `|‖z‖ - r| ≤ ‖circleMap z r θ‖`. -/
lemma abs_norm_sub_le_norm_circleMap (z : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    |‖z‖ - r| ≤ ‖circleMap z r θ‖ := by
  have hw : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hc : circleMap z r θ = z + (r : ℂ) * Complex.exp (θ * Complex.I) := rfl
  rw [hc]
  have h1 := norm_sub_le (z + (r : ℂ) * Complex.exp (θ * Complex.I)) ((r : ℂ) * Complex.exp (θ * Complex.I))
  have h2 := norm_sub_le (z + (r : ℂ) * Complex.exp (θ * Complex.I)) z
  rw [add_sub_cancel_right, hw] at h1
  rw [add_sub_cancel_left, hw] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Upper bound on a circle: `‖circleMap z r θ‖ ≤ ‖z‖ + r`. -/
lemma norm_circleMap_le_add (z : ℂ) {r : ℝ} (hr : 0 < r) (θ : ℝ) : ‖circleMap z r θ‖ ≤ ‖z‖ + r := by
  have hc : circleMap z r θ = z + (r : ℂ) * Complex.exp (θ * Complex.I) := rfl
  rw [hc]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hr]

/-- The modulus of a point of a circle is a measurable function of the angle. -/
lemma measurable_norm_circleMap (z : ℂ) (r : ℝ) : Measurable fun θ : ℝ => ‖circleMap z r θ‖ :=
  (continuous_norm.comp (continuous_circleMap z r)).measurable

/-- The interval `(0, 2π]` has finite Lebesgue measure. -/
lemma volume_Ioc_two_pi_ne_top : volume (Ioc (0 : ℝ) (2 * π)) ≠ ∞ := by
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

/-- `θ ↦ log |cos((θ-α)/2)|` is interval integrable on `[0, 2π]`: `Real.intervalIntegrable_log_cos` on the
rescaled and shifted interval. -/
lemma intervalIntegrable_log_cos_affine (α : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.log (Real.cos ((θ - α) / 2))) volume 0 (2 * π) := by
  have h1 := (intervalIntegrable_log_cos (a := -α / 2) (b := (2 * π - α) / 2)).comp_mul_left
    (c := (1 / 2 : ℝ))
  have h2 := h1.comp_sub_right α
  have ea : -α / 2 / (1 / 2) + α = 0 := by ring
  have eb : (2 * π - α) / 2 / (1 / 2) + α = 2 * π := by ring
  rw [ea, eb] at h2
  convert h2 using 1
  funext θ
  simp only [Function.comp]
  rw [show (θ - α) / 2 = 1 / 2 * (θ - α) by ring]

/-- **Tangent case, deterministic.** If `‖z‖ = r`, the function `θ ↦ 1_{‖circleMap z r θ‖ ≤ 1} (-log ‖circleMap z r θ‖)`
is integrable on `(0, 2π]`: its logarithmic singularity at the (at most one) point where the circle meets the origin is
the one of `log |cos|`. -/
lemma integrableOn_log_small_tangent {r : ℝ} (hr : 0 < r) (α : ℝ) :
    IntegrableOn (fun θ : ℝ => Set.indicator {θ : ℝ | ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖ ≤ 1}
      (fun θ : ℝ => -Real.log ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖) θ) (Ioc 0 (2 * π)) := by
  have hρ := measurable_norm_circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r
  have hmeas : Measurable fun θ : ℝ => Set.indicator {θ : ℝ | ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖ ≤ 1}
      (fun θ : ℝ => -Real.log ‖circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ‖) θ :=
    ((Real.measurable_log.comp hρ).neg).indicator (measurableSet_le hρ measurable_const)
  have hl : IntegrableOn (fun θ : ℝ => ‖Real.log (Real.cos ((θ - α) / 2))‖) (Ioc 0 (2 * π)) :=
    (intervalIntegrable_log_cos_affine α).norm.1
  have hc : IntegrableOn (fun _ : ℝ => |Real.log (2 * r)|) (Ioc 0 (2 * π)) :=
    integrableOn_const volume_Ioc_two_pi_ne_top
  refine Integrable.mono' (Integrable.add hc hl) hmeas.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs with hθ
  · rcases (norm_nonneg (circleMap ((r : ℂ) * Complex.exp (α * Complex.I)) r θ)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero, neg_zero, norm_zero]
      exact add_nonneg (abs_nonneg _) (norm_nonneg _)
    · rw [norm_circleMap_tangent hr] at hpos ⊢
      have hcos : |Real.cos ((θ - α) / 2)| ≠ 0 := by
        intro h
        rw [h, mul_zero] at hpos
        exact lt_irrefl _ hpos
      have hlog : Real.log (2 * r * |Real.cos ((θ - α) / 2)|)
          = Real.log (2 * r) + Real.log (Real.cos ((θ - α) / 2)) := by
        rw [Real.log_mul (mul_pos two_pos hr).ne' hcos, Real.log_abs]
      rw [hlog]
      calc ‖-(Real.log (2 * r) + Real.log (Real.cos ((θ - α) / 2)))‖
          = ‖Real.log (2 * r) + Real.log (Real.cos ((θ - α) / 2))‖ := norm_neg _
        _ ≤ ‖Real.log (2 * r)‖ + ‖Real.log (Real.cos ((θ - α) / 2))‖ := norm_add_le _ _
        _ = |Real.log (2 * r)| + ‖Real.log (Real.cos ((θ - α) / 2))‖ := by rw [Real.norm_eq_abs]
  · simp only [norm_zero]
    exact add_nonneg (abs_nonneg _) (norm_nonneg _)

/-- **Integrability of the small-radius logarithm on a circle.** For `r > 0`, the function
`θ ↦ 1_{‖circleMap z r θ‖ ≤ 1} (-log ‖circleMap z r θ‖)` is integrable on `(0, 2π]`. If `‖z‖ ≠ r` the circle keeps
distance `|‖z‖ - r| > 0` from the origin; if `‖z‖ = r` this is `integrableOn_log_small_tangent`. -/
lemma integrableOn_log_small_circleMap (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun θ : ℝ => Set.indicator {θ : ℝ | ‖circleMap z r θ‖ ≤ 1}
      (fun θ : ℝ => -Real.log ‖circleMap z r θ‖) θ) (Ioc 0 (2 * π)) := by
  by_cases hz : ‖z‖ = r
  · obtain ⟨α, rfl⟩ : ∃ α : ℝ, z = (r : ℂ) * Complex.exp (α * Complex.I) := by
      refine ⟨Complex.arg z, ?_⟩
      have h := Complex.norm_mul_exp_arg_mul_I z
      rw [hz] at h
      exact h.symm
    exact integrableOn_log_small_tangent hr α
  · have hρ := measurable_norm_circleMap z r
    have hmeas : Measurable fun θ : ℝ => Set.indicator {θ : ℝ | ‖circleMap z r θ‖ ≤ 1}
        (fun θ : ℝ => -Real.log ‖circleMap z r θ‖) θ :=
      ((Real.measurable_log.comp hρ).neg).indicator (measurableSet_le hρ measurable_const)
    have hδ : 0 < |‖z‖ - r| := abs_pos.2 (sub_ne_zero.2 hz)
    have hc : IntegrableOn (fun _ : ℝ => |Real.log (|‖z‖ - r|)|) (Ioc 0 (2 * π)) :=
      integrableOn_const volume_Ioc_two_pi_ne_top
    refine Integrable.mono' hc hmeas.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hθ
    · have hlow := abs_norm_sub_le_norm_circleMap z hr θ
      have hl1 : Real.log |‖z‖ - r| ≤ Real.log ‖circleMap z r θ‖ := Real.log_le_log hδ hlow
      have hl2 : 0 ≤ -Real.log ‖circleMap z r θ‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hθ)
      have hB : -Real.log |‖z‖ - r| ≤ |Real.log (|‖z‖ - r|)| := neg_le_abs _
      rw [Real.norm_eq_abs, abs_of_nonneg hl2]
      linarith
    · simp only [norm_zero]
      exact abs_nonneg _

end LatticeProb.CircleLogIntegrals
