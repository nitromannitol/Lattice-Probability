/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.GreenSquareCut at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareGreen6
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
`cutoff a L δ u = S((u−a)/δ − 1) S((a+L−u)/δ − 1)` (`S` = mathlib `Real.smoothTransition`)
vanishes within `δ` of `{a, a+L}`, equals `1` beyond `2δ`, and its derivative is `O(1/δ)` on
the transition layers, where `|sin(πk(u−a)/L)| ≤ (πk/L)·dist(u, {a, a+L})`. Hence
`|cutoff' · sinMode| ≤ 2 (πk/L) M` uniformly in `δ` (`HeatSq.abs_cutoffD_mul_sinMode_le`).
This is the cutoff step of the standard proof that a Lipschitz function vanishing on `∂U` lies in
`H¹₀(U)` (Evans, *PDE*, §5.5, Thm 2); own elementary implementation.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology

namespace LQGMetric
namespace HeatSq

local notation "S" => Real.smoothTransition

lemma deriv_smoothTransition_eq_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) : deriv S t = 0 := by
  rcases ht with ht | ht
  · have : S =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      (eventually_lt_nhds ht).mono fun x hx => Real.smoothTransition.zero_of_nonpos hx.le
    rw [this.deriv_eq]; simp
  · have : S =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
      (eventually_gt_nhds ht).mono fun x hx => Real.smoothTransition.one_of_one_le hx.le
    rw [this.deriv_eq]; simp

lemma continuous_deriv_smoothTransition : Continuous (deriv S) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

/-- `|S'(t)| (|t| + 1)` is bounded -/
lemma exists_bound_deriv_smoothTransition : ∃ M, ∀ t, |deriv S t| * (|t| + 1) ≤ M := by
  have hc : Continuous fun t => |deriv S t| * (|t| + 1) :=
    (continuous_deriv_smoothTransition.abs).mul (continuous_abs.add continuous_const)
  have hs : HasCompactSupport fun t => |deriv S t| * (|t| + 1) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun t ht => ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    rw [deriv_smoothTransition_eq_zero ht, abs_zero, zero_mul]
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hc
  exact ⟨M, fun t => (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hM t)⟩

/-- the cutoff vanishing within `δ` of `{a, a+L}` and equal to `1` beyond `2δ` -/
def cutoff (a L δ u : ℝ) : ℝ := S ((u - a) / δ - 1) * S ((a + L - u) / δ - 1)

/-- its derivative -/
def cutoffD (a L δ u : ℝ) : ℝ :=
  deriv S ((u - a) / δ - 1) / δ * S ((a + L - u) / δ - 1) -
    S ((u - a) / δ - 1) * (deriv S ((a + L - u) / δ - 1) / δ)

lemma hasDerivAt_smoothTransition (t : ℝ) : HasDerivAt S (deriv S t) t :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt

lemma hasDerivAt_cutoff (a L δ u : ℝ) : HasDerivAt (cutoff a L δ) (cutoffD a L δ u) u := by
  have h1 : HasDerivAt (fun u => (u - a) / δ - 1) (1 / δ) u := by
    simpa using (((hasDerivAt_id u).sub_const a).div_const δ).sub_const 1
  have h2 : HasDerivAt (fun u => (a + L - u) / δ - 1) (-1 / δ) u := by
    simpa using (((hasDerivAt_id u).const_sub (a + L)).div_const δ).sub_const 1
  have := ((hasDerivAt_smoothTransition _).comp u h1).mul
    ((hasDerivAt_smoothTransition _).comp u h2)
  have e : cutoff a L δ = (S ∘ fun u => (u - a) / δ - 1) * (S ∘ fun u => (a + L - u) / δ - 1) :=
    rfl
  rw [e]
  refine this.congr_deriv ?_
  unfold cutoffD
  simp only [Function.comp_apply]
  ring

lemma contDiff_cutoff (a L δ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoff a L δ) := by
  unfold cutoff
  have := Real.smoothTransition.contDiff (n := ⊤)
  exact (this.comp (by fun_prop)).mul (this.comp (by fun_prop))

lemma cutoff_nonneg (a L δ u : ℝ) : 0 ≤ cutoff a L δ u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma cutoff_le_one (a L δ u : ℝ) : cutoff a L δ u ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

lemma cutoff_eq_zero {a L δ u : ℝ} (hδ : 0 < δ) (hu : u ≤ a + δ ∨ a + L - δ ≤ u) :
    cutoff a L δ u = 0 := by
  unfold cutoff
  rcases hu with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    rw [sub_nonpos, div_le_one hδ]; linarith
  · rw [Real.smoothTransition.zero_of_nonpos (x := (a + L - u) / δ - 1), mul_zero]
    rw [sub_nonpos, div_le_one hδ]; linarith

lemma cutoff_eq_one {a L δ u : ℝ} (hδ : 0 < δ) (h1 : a + 2 * δ ≤ u) (h2 : u ≤ a + L - 2 * δ) :
    cutoff a L δ u = 1 := by
  unfold cutoff
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, one_mul]
  · rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith
  · rw [le_sub_iff_add_le, le_div_iff₀ hδ]; linarith

lemma abs_sinMode_le_left {L : ℝ} (hL : 0 < L) (a : ℝ) (k : ℕ) (u : ℝ) :
    |sinMode a L k u| ≤ π * k / L * |u - a| := by
  rw [sinMode_eq]
  refine (Real.abs_sin_le_abs).trans_eq ?_
  rw [abs_mul, abs_of_nonneg (by positivity)]

lemma abs_sinMode_le_right {L : ℝ} (hL : 0 < L) (a : ℝ) (k : ℕ) (u : ℝ) :
    |sinMode a L k u| ≤ π * k / L * |a + L - u| := by
  rw [sinMode_eq]
  have e : π * k / L * (u - a) = k * π - π * k / L * (a + L - u) := by
    field_simp; ring
  rw [e, Real.sin_nat_mul_pi_sub, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  refine (Real.abs_sin_le_abs).trans_eq ?_
  rw [abs_mul, abs_of_nonneg (by positivity)]

lemma abs_sub_le_mul_of_eq {x δ t : ℝ} (hδ : 0 < δ) (h : t = x / δ - 1) :
    |x| ≤ δ * (|t| + 1) := by
  have e : x = δ * (t + 1) := by rw [h]; field_simp; ring
  rw [e, abs_mul, abs_of_pos hδ]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by simp)) hδ.le

/-- **The cutoff derivative against a sine mode is bounded uniformly in `δ`.** -/
lemma abs_cutoffD_mul_sinMode_le {a L δ M : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hM : ∀ t, |deriv S t| * (|t| + 1) ≤ M) (k : ℕ) (u : ℝ) :
    |cutoffD a L δ u * sinMode a L k u| ≤ 2 * (π * k / L) * M := by
  set t₁ := (u - a) / δ - 1
  set t₂ := (a + L - u) / δ - 1
  set c := π * k / L
  have hc : 0 ≤ c := by positivity
  have e1 : |u - a| ≤ δ * (|t₁| + 1) := abs_sub_le_mul_of_eq hδ rfl
  have e2 : |a + L - u| ≤ δ * (|t₂| + 1) := abs_sub_le_mul_of_eq hδ rfl
  have hA : |deriv S t₁ / δ * S t₂ * sinMode a L k u| ≤ c * M := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hδ,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    have hs := abs_sinMode_le_left hL a k u
    calc |deriv S t₁| / δ * S t₂ * |sinMode a L k u|
        ≤ |deriv S t₁| / δ * 1 * (c * (δ * (|t₁| + 1))) := by
          gcongr
          · exact Real.smoothTransition.le_one _
          · exact hs.trans (mul_le_mul_of_nonneg_left e1 hc)
      _ = c * (|deriv S t₁| * (|t₁| + 1)) := by field_simp
      _ ≤ c * M := mul_le_mul_of_nonneg_left (hM t₁) hc
  have hB : |S t₁ * (deriv S t₂ / δ) * sinMode a L k u| ≤ c * M := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hδ,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    have hs := abs_sinMode_le_right hL a k u
    calc S t₁ * (|deriv S t₂| / δ) * |sinMode a L k u|
        ≤ 1 * (|deriv S t₂| / δ) * (c * (δ * (|t₂| + 1))) := by
          gcongr
          · exact Real.smoothTransition.le_one _
          · exact hs.trans (mul_le_mul_of_nonneg_left e2 hc)
      _ = c * (|deriv S t₂| * (|t₂| + 1)) := by field_simp
      _ ≤ c * M := mul_le_mul_of_nonneg_left (hM t₂) hc
  have : cutoffD a L δ u * sinMode a L k u =
      deriv S t₁ / δ * S t₂ * sinMode a L k u - S t₁ * (deriv S t₂ / δ) * sinMode a L k u := by
    unfold cutoffD; ring
  rw [this]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ c * M + c * M := add_le_add hA hB
    _ = _ := by ring

end HeatSq
end LQGMetric
