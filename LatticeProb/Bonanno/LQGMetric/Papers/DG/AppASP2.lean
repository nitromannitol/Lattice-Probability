/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppASP2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppASP
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L7Trunc

/-!
# Ding–Gwynne App. A: exit bounds for `a_x = p − p_D` (task P2-DG3B)

Continuation of `AppASP`. With `eB ρ τ = (πτ)⁻¹ e^{−ρ²/(9τ)}`:

* `lintegral_sq_compK_le` — if `B(x, ρ) ⊆ D` then `‖a_x(τ)‖₂² ≤ eB ρ τ`: pointwise
  `(p − p_D)² ≤ p² − p_D²`, Chapman–Kolmogorov, and DZZ's reflection bound for the bridge from `x`
  to `x` leaving `B(x, ρ)` (`DZZ.killedHeat_sub_inter_ball_le`, DZZ l. 557);
* `lintegral_sq_compK_sub_le_exit` — `‖a_x(τ) − a_c(τ)‖₂² ≤ 4 eB ρ τ`;
* `lintegral_sq_compK_sub_le_split` — `‖a_x(τ₁+τ₂) − a_c(τ₁+τ₂)‖₂² ≤
  2|x − c|²/(8πτ₁²) + 8 eB ρ τ₁` (with `AppASP.lintegral_sq_compK_sub_le`).

These are the inputs of the time integration in DG Lemma A.2 (DG:2183–2232; own semigroup route,
DEVIATIONS DG3B-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat

/-- The exit bound `(πτ)⁻¹ e^{−ρ²/(9τ)}`. -/
def eB (ρ τ : ℝ) : ℝ := (Real.pi * τ)⁻¹ * Real.exp (-(ρ ^ 2 / (9 * τ)))

lemma eB_nonneg (ρ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ eB ρ τ := by
  unfold eB; have := Real.pi_pos; positivity

/-- `‖a_x(τ)‖₂² ≤ eB ρ τ` when `B(x, ρ) ⊆ D`. -/
theorem lintegral_sq_compK_le {D : Set ℂ} (hD : IsOpen D) {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hxD : Metric.ball x ρ ⊆ D) {τ : ℝ≥0} (hτ : τ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal (compK D τ x w ^ 2) ≤ ENNReal.ofReal (eB ρ τ) := by
  have hτ' := pos_of_ne hτ
  have hpt : ∀ w, compK D τ x w ^ 2 ≤
      heatKernel τ x w * heatKernel τ x w - killedHeat D τ x w * killedHeat D τ x w := by
    intro w
    unfold compK
    have := killedHeat_nonneg D τ x w
    have := killedHeat_le_heatKernel D τ x w
    nlinarith
  have hnn : ∀ w, 0 ≤
      heatKernel τ x w * heatKernel τ x w - killedHeat D τ x w * killedHeat D τ x w := by
    intro w
    have := killedHeat_nonneg D τ x w
    have := killedHeat_le_heatKernel D τ x w
    nlinarith
  have hint : Integrable fun w =>
      heatKernel τ x w * heatKernel τ x w - killedHeat D τ x w * killedHeat D τ x w :=
    (WhiteNoise.integrable_heatKernel_mul_heatKernel _ hτ' x x).sub
      (integrable_killedHeat_mul hD hD hτ x)
  have hval : ∫ w, (heatKernel τ x w * heatKernel τ x w -
      killedHeat D τ x w * killedHeat D τ x w) =
      heatKernel ((τ + τ : ℝ≥0) : ℝ) x x - killedHeat D (τ + τ) x x := by
    rw [integral_sub (WhiteNoise.integrable_heatKernel_mul_heatKernel _ hτ' x x)
      (integrable_killedHeat_mul hD hD hτ x), WhiteNoise.integral_heatKernel_mul_heatKernel _ hτ',
      integral_killedHeat_mul_killedHeat hD hτ x x, NNReal.coe_add, two_mul]
  have hττ : τ + τ ≠ 0 := by positivity
  have hdzz := DZZ.killedHeat_sub_inter_ball_le hττ Set.univ x hρ
  rw [killedHeat_univ, Set.univ_inter] at hdzz
  have hmono := killedHeat_mono hxD (τ + τ) x x
  calc ∫⁻ w, ENNReal.ofReal (compK D τ x w ^ 2)
      ≤ ∫⁻ w, ENNReal.ofReal (heatKernel τ x w * heatKernel τ x w -
          killedHeat D τ x w * killedHeat D τ x w) :=
        lintegral_mono fun w => ENNReal.ofReal_le_ofReal (hpt w)
    _ = ENNReal.ofReal (heatKernel ((τ + τ : ℝ≥0) : ℝ) x x - killedHeat D (τ + τ) x x) := by
        rw [← hval, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)]
    _ ≤ ENNReal.ofReal (eB ρ τ) := by
        refine ENNReal.ofReal_le_ofReal ((sub_le_sub_left hmono _).trans (hdzz.trans
          (le_of_eq ?_)))
        unfold eB
        rw [NNReal.coe_add]
        have := Real.pi_pos
        rw [show -(2 * (ρ / 3) ^ 2 / ((τ : ℝ) + τ)) = -(ρ ^ 2 / (9 * τ)) by field_simp; ring]
        field_simp
        ring

lemma ofReal_sq_sub_le (a b : ℝ) :
    ENNReal.ofReal ((a - b) ^ 2) ≤ 2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a + b)])

/-- `‖a_x(τ) − a_c(τ)‖₂² ≤ 4 eB ρ τ` when `B(x, ρ), B(c, ρ) ⊆ D`. -/
theorem lintegral_sq_compK_sub_le_exit {D : Set ℂ} (hD : IsOpen D) {x c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hxD : Metric.ball x ρ ⊆ D) (hcD : Metric.ball c ρ ⊆ D) {τ : ℝ≥0}
    (hτ : τ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal ((compK D τ x w - compK D τ c w) ^ 2) ≤
      4 * ENNReal.ofReal (eB ρ τ) := by
  calc ∫⁻ w, ENNReal.ofReal ((compK D τ x w - compK D τ c w) ^ 2)
      ≤ ∫⁻ w, (2 * ENNReal.ofReal (compK D τ x w ^ 2) +
          2 * ENNReal.ofReal (compK D τ c w ^ 2)) :=
        lintegral_mono fun w => ofReal_sq_sub_le _ _
    _ = 2 * (∫⁻ w, ENNReal.ofReal (compK D τ x w ^ 2)) +
          2 * ∫⁻ w, ENNReal.ofReal (compK D τ c w ^ 2) := by
        rw [lintegral_add_left' ((((measurable_compK_right hD hτ x).pow_const 2).ennreal_ofReal
          ).const_mul 2).aemeasurable, lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
    _ ≤ 2 * ENNReal.ofReal (eB ρ τ) + 2 * ENNReal.ofReal (eB ρ τ) := by
        gcongr
        · exact lintegral_sq_compK_le hD hρ hxD hτ
        · exact lintegral_sq_compK_le hD hρ hcD hτ
    _ = 4 * ENNReal.ofReal (eB ρ τ) := by ring

/-- `‖a_x(τ₁+τ₂) − a_c(τ₁+τ₂)‖₂² ≤ 2|x − c|²/(8πτ₁²) + 8 eB ρ τ₁`. -/
theorem lintegral_sq_compK_sub_le_split {D : Set ℂ} (hD : IsOpen D) {x c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hxD : Metric.ball x ρ ⊆ D) (hcD : Metric.ball c ρ ⊆ D) {τ₁ τ₂ : ℝ≥0}
    (h₁ : τ₁ ≠ 0) (h₂ : τ₂ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal ((compK D (τ₁ + τ₂) x w - compK D (τ₁ + τ₂) c w) ^ 2) ≤
      2 * ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (τ₁ : ℝ) ^ 2)) +
        8 * ENNReal.ofReal (eB ρ τ₁) := by
  refine (lintegral_sq_compK_sub_le hD h₁ h₂ x c).trans ?_
  have h := lintegral_sq_compK_sub_le_exit hD hρ hxD hcD h₁
  calc 2 * ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (τ₁ : ℝ) ^ 2)) +
        2 * ∫⁻ y, ENNReal.ofReal ((compK D τ₁ x y - compK D τ₁ c y) ^ 2)
      ≤ 2 * ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (τ₁ : ℝ) ^ 2)) +
        2 * (4 * ENNReal.ofReal (eB ρ τ₁)) := by gcongr
    _ = _ := by ring

/-- `eB ρ τ ≤ 4374 τ²/(π ρ⁶)` (from `e^y ≥ y³/6`). -/
lemma eB_le_sq {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    eB ρ τ ≤ 4374 / (Real.pi * ρ ^ 6) * τ ^ 2 := by
  have hpi := Real.pi_pos
  set y := ρ ^ 2 / (9 * τ) with hy
  have hy0 : 0 < y := by positivity
  have h3 := Real.pow_div_factorial_le_exp y hy0.le 3
  have hfac : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h3
  have hexp : Real.exp (-y) ≤ 6 / y ^ 3 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos y) (by positivity), inv_div]
    exact h3
  unfold eB
  calc (Real.pi * τ)⁻¹ * Real.exp (-y) ≤ (Real.pi * τ)⁻¹ * (6 / y ^ 3) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 4374 / (Real.pi * ρ ^ 6) * τ ^ 2 := by
        rw [hy]; field_simp; ring

/-- **Uniform start-point bound**: if `B(x, ρ), B(c, ρ) ⊆ D` then for every `τ > 0`,
`‖a_x(τ) − a_c(τ)‖₂² ≤ (1/(4π) + 34992/(πρ⁶)) |x − c|` (split at `τ₁ = |x − c|^{1/2}` when
`τ > |x − c|^{1/2}`, exit bound otherwise). -/
theorem lintegral_sq_compK_sub_le_unif {D : Set ℂ} (hD : IsOpen D) {x c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hxD : Metric.ball x ρ ⊆ D) (hcD : Metric.ball c ρ ⊆ D) {τ : ℝ≥0}
    (hτ : τ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal ((compK D τ x w - compK D τ c w) ^ 2) ≤
      ENNReal.ofReal ((1 / (4 * Real.pi) + 34992 / (Real.pi * ρ ^ 6)) * ‖x - c‖) := by
  have hpi := Real.pi_pos
  have hτ' := pos_of_ne hτ
  set δ := ‖x - c‖ with hδ
  rcases (norm_nonneg (x - c)).eq_or_lt with h0 | hδ0
  · have hxc : x = c := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    subst hxc
    simp
  have hC : 0 ≤ 4374 / (Real.pi * ρ ^ 6) := by positivity
  by_cases hcase : (τ : ℝ) ≤ Real.sqrt δ
  · refine (lintegral_sq_compK_sub_le_exit hD hρ hxD hcD hτ).trans ?_
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
    rw [h4, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : (τ : ℝ) ^ 2 ≤ δ := by
      calc (τ : ℝ) ^ 2 ≤ Real.sqrt δ ^ 2 := pow_le_pow_left₀ hτ'.le hcase 2
        _ = δ := Real.sq_sqrt hδ0.le
    calc 4 * eB ρ τ ≤ 4 * (4374 / (Real.pi * ρ ^ 6) * (τ : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (eB_le_sq hρ hτ') (by norm_num)
      _ ≤ 4 * (4374 / (Real.pi * ρ ^ 6) * δ) := by gcongr
      _ ≤ (1 / (4 * Real.pi) + 34992 / (Real.pi * ρ ^ 6)) * δ := by
          have : 0 ≤ 1 / (4 * Real.pi) * δ := by positivity
          have e : 34992 / (Real.pi * ρ ^ 6) = 8 * (4374 / (Real.pi * ρ ^ 6)) := by ring
          rw [add_mul, e]
          nlinarith [mul_nonneg hC hδ0.le]
  · push Not at hcase
    set τ₁ : ℝ≥0 := (Real.sqrt δ).toNNReal with hτ₁
    have hτ₁v : (τ₁ : ℝ) = Real.sqrt δ := Real.coe_toNNReal _ (Real.sqrt_nonneg _)
    have hτ₁0 : τ₁ ≠ 0 := by
      intro h; rw [h, NNReal.coe_zero] at hτ₁v
      exact (Real.sqrt_pos.2 hδ0).ne' hτ₁v.symm
    have hlt : τ₁ < τ := by rw [← NNReal.coe_lt_coe, hτ₁v]; exact hcase
    have hτ₂0 : τ - τ₁ ≠ 0 := (tsub_pos_of_lt hlt).ne'
    have hsum : τ₁ + (τ - τ₁) = τ := add_tsub_cancel_of_le hlt.le
    have h := lintegral_sq_compK_sub_le_split hD hρ hxD hcD hτ₁0 hτ₂0
    rw [hsum] at h
    refine h.trans ?_
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    have h8 : (8 : ℝ≥0∞) = ENNReal.ofReal 8 := by simp
    have hsq : (τ₁ : ℝ) ^ 2 = δ := by rw [hτ₁v, Real.sq_sqrt hδ0.le]
    have hE0 : 0 ≤ 8 * eB ρ τ₁ := mul_nonneg (by norm_num) (eB_nonneg ρ (NNReal.coe_nonneg τ₁))
    rw [h2, h8, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) hE0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hE := eB_le_sq hρ (pos_of_ne hτ₁0)
    rw [hsq] at hE
    rw [← hδ, hsq]
    have e1 : 2 * (δ ^ 2 / (8 * Real.pi * δ)) = 1 / (4 * Real.pi) * δ := by
      field_simp; ring
    rw [e1, add_mul]
    have e : 34992 / (Real.pi * ρ ^ 6) = 8 * (4374 / (Real.pi * ρ ^ 6)) := by ring
    rw [e]
    nlinarith

end DG
end LQGMetric
