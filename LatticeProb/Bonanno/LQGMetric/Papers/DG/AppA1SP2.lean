/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppA1SP2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA1SP

/-!
# Ding–Gwynne Lemma A.1: start-point regularity of `p_U − p_D`, part 2 (task P2-DG3B)

Generalization of `AppASP.lintegral_sq_compK_sub_le` and `AppASP2` to `a_x = p_U − p_D`
(`compK2`, `D ⊆ U`), ending with the uniform bound `lintegral_sq_compK2_sub_le_unif`:
`‖a_x(τ) − a_c(τ)‖₂² ≤ (3/(4π) + 87480/(πρ⁶)) |x − c|` if `B(x,ρ), B(c,ρ) ⊆ D`.
Own semigroup route (DEVIATIONS DG3B-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat

/-- Schur's test on both terms of `compK2_split`. -/
theorem lintegral_sq_compK2_sub_le {U D : Set ℂ} (hU : IsOpen U) (hD : IsOpen D) (hDU : D ⊆ U)
    {τ₁ τ₂ : ℝ≥0} (h₁ : τ₁ ≠ 0) (h₂ : τ₂ ≠ 0) (x c : ℂ) :
    ∫⁻ w, ENNReal.ofReal ((compK2 U D (τ₁ + τ₂) x w - compK2 U D (τ₁ + τ₂) c w) ^ 2) ≤
      2 * (∫⁻ y, ENNReal.ofReal ((killedHeat U τ₁ x y - killedHeat U τ₁ c y) ^ 2)) +
        2 * ∫⁻ y, ENNReal.ofReal ((compK2 U D τ₁ x y - compK2 U D τ₁ c y) ^ 2) := by
  have hh0 : ∀ (t : ℝ≥0) (a b : ℂ), 0 ≤ heatKernel t a b := fun t a b => heatKernel_nonneg' t a b
  set T₁ : ℂ → ℝ := fun w => ∫ y, (killedHeat U τ₁ x y - killedHeat U τ₁ c y) * compK2 U D τ₂ y w
  set T₂ : ℂ → ℝ := fun w => ∫ y, (compK2 U D τ₁ x y - compK2 U D τ₁ c y) * killedHeat D τ₂ y w
  have iA : ∀ (u w : ℂ), Integrable fun y => killedHeat U τ₁ u y * compK2 U D τ₂ y w := by
    intro u w
    refine integrable_of_le_heat_mul h₁ h₂ u w ((measurable_killedHeat_right hU h₁ u).mul
      (measurable_compK2_left hU hD h₂ w)) fun y => ?_
    rw [abs_of_nonneg (mul_nonneg (killedHeat_nonneg _ _ _ _) (compK2_nonneg hDU _ _ _))]
    exact mul_le_mul (killedHeat_le_heatKernel _ _ _ _) (compK2_le _ _ _ _ _)
      (compK2_nonneg hDU _ _ _) (hh0 _ _ _)
  have iB : ∀ (u w : ℂ), Integrable fun y => compK2 U D τ₁ u y * killedHeat D τ₂ y w := by
    intro u w
    refine integrable_of_le_heat_mul h₁ h₂ u w ((measurable_compK2_right hU hD h₁ u).mul
      (measurable_killedHeat_left hD h₂ w)) fun y => ?_
    rw [abs_of_nonneg (mul_nonneg (compK2_nonneg hDU _ _ _) (killedHeat_nonneg _ _ _ _))]
    exact mul_le_mul (compK2_le _ _ _ _ _) (killedHeat_le_heatKernel _ _ _ _)
      (killedHeat_nonneg _ _ _ _) (hh0 _ _ _)
  have hsplit : ∀ w, compK2 U D (τ₁ + τ₂) x w - compK2 U D (τ₁ + τ₂) c w = T₁ w + T₂ w := by
    intro w
    rw [compK2_split hU hD hDU h₁ h₂ x w, compK2_split hU hD hDU h₁ h₂ c w]
    simp only [T₁, T₂, sub_mul]
    rw [integral_sub (iA x w) (iA c w), integral_sub (iB x w) (iB c w)]
    ring
  have hpt : ∀ w, ENNReal.ofReal ((compK2 U D (τ₁ + τ₂) x w - compK2 U D (τ₁ + τ₂) c w) ^ 2) ≤
      2 * ENNReal.ofReal (T₁ w ^ 2) + 2 * ENNReal.ofReal (T₂ w ^ 2) := by
    intro w
    rw [hsplit w]
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (T₁ w - T₂ w)])
  have hT₁m : Measurable T₁ := by
    refine (StronglyMeasurable.integral_prod_left (f := fun y w =>
      (killedHeat U τ₁ x y - killedHeat U τ₁ c y) * compK2 U D τ₂ y w) ?_).measurable
    exact ((((measurable_killedHeat_right hU h₁ x).sub (measurable_killedHeat_right hU h₁ c)).comp
      measurable_fst).mul ((measurable_killedHeat_uncurry hU τ₂).sub
        (measurable_killedHeat_uncurry hD τ₂))).stronglyMeasurable
  have hS₁ := lintegral_sq_integral_le (f := fun y => killedHeat U τ₁ x y - killedHeat U τ₁ c y)
    (G := fun y w => compK2 U D τ₂ y w) (K := fun y w => heatKernel τ₂ y w)
    ((measurable_killedHeat_right hU h₁ x).sub (measurable_killedHeat_right hU h₁ c))
    (measurable_heatKernel_uncurry _)
    (fun y w => by rw [abs_of_nonneg (compK2_nonneg hDU _ _ _)]; exact compK2_le _ _ _ _ _)
    (lintegral_heat_left_le h₂) (lintegral_heat_right_le h₂)
  have hS₂ := lintegral_sq_integral_le (f := fun y => compK2 U D τ₁ x y - compK2 U D τ₁ c y)
    (G := fun y w => killedHeat D τ₂ y w) (K := fun y w => heatKernel τ₂ y w)
    ((measurable_compK2_right hU hD h₁ x).sub (measurable_compK2_right hU hD h₁ c))
    (measurable_heatKernel_uncurry _)
    (fun y w => by
      rw [abs_of_nonneg (killedHeat_nonneg _ _ _ _)]; exact killedHeat_le_heatKernel _ _ _ _)
    (lintegral_heat_left_le h₂) (lintegral_heat_right_le h₂)
  calc ∫⁻ w, ENNReal.ofReal ((compK2 U D (τ₁ + τ₂) x w - compK2 U D (τ₁ + τ₂) c w) ^ 2)
      ≤ ∫⁻ w, (2 * ENNReal.ofReal (T₁ w ^ 2) + 2 * ENNReal.ofReal (T₂ w ^ 2)) :=
        lintegral_mono hpt
    _ = 2 * (∫⁻ w, ENNReal.ofReal (T₁ w ^ 2)) + 2 * ∫⁻ w, ENNReal.ofReal (T₂ w ^ 2) := by
        rw [lintegral_add_left' (((hT₁m.pow_const 2).ennreal_ofReal).const_mul 2).aemeasurable,
          lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
    _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ zero_le)
          (mul_le_mul_of_nonneg_left ?_ zero_le)
        · exact hS₁
        · exact hS₂


/-- `‖a_x(τ) − a_c(τ)‖₂² ≤ 4 eB ρ τ`. -/
theorem lintegral_sq_compK2_sub_le_exit {U D : Set ℂ} (hU : IsOpen U) (hD : IsOpen D)
    (hDU : D ⊆ U) {x c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hxD : Metric.ball x ρ ⊆ D)
    (hcD : Metric.ball c ρ ⊆ D) {τ : ℝ≥0} (hτ : τ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal ((compK2 U D τ x w - compK2 U D τ c w) ^ 2) ≤
      4 * ENNReal.ofReal (eB ρ τ) := by
  calc ∫⁻ w, ENNReal.ofReal ((compK2 U D τ x w - compK2 U D τ c w) ^ 2)
      ≤ ∫⁻ w, (2 * ENNReal.ofReal (compK2 U D τ x w ^ 2) +
          2 * ENNReal.ofReal (compK2 U D τ c w ^ 2)) :=
        lintegral_mono fun w => ofReal_sq_sub_le _ _
    _ = 2 * (∫⁻ w, ENNReal.ofReal (compK2 U D τ x w ^ 2)) +
          2 * ∫⁻ w, ENNReal.ofReal (compK2 U D τ c w ^ 2) := by
        rw [lintegral_add_left' ((((measurable_compK2_right hU hD hτ x).pow_const 2
          ).ennreal_ofReal).const_mul 2).aemeasurable, lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
    _ ≤ 2 * ENNReal.ofReal (eB ρ τ) + 2 * ENNReal.ofReal (eB ρ τ) := by
        gcongr
        · exact lintegral_sq_compK2_le hD hDU hρ hxD hτ
        · exact lintegral_sq_compK2_le hD hDU hρ hcD hτ
    _ = 4 * ENNReal.ofReal (eB ρ τ) := by ring

/-- **Uniform start-point bound for `p_U − p_D`**. -/
theorem lintegral_sq_compK2_sub_le_unif {U D : Set ℂ} (hU : IsOpen U) (hD : IsOpen D)
    (hDU : D ⊆ U) {x c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hxD : Metric.ball x ρ ⊆ D)
    (hcD : Metric.ball c ρ ⊆ D) {τ : ℝ≥0} (hτ : τ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal ((compK2 U D τ x w - compK2 U D τ c w) ^ 2) ≤
      ENNReal.ofReal ((3 / (4 * Real.pi) + 87480 / (Real.pi * ρ ^ 6)) * ‖x - c‖) := by
  have hpi := Real.pi_pos
  have hτ' := pos_of_ne hτ
  set δ := ‖x - c‖ with hδ
  rcases (norm_nonneg (x - c)).eq_or_lt with h0 | hδ0
  · have hxc : x = c := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    subst hxc
    simp
  have hC : 0 ≤ 4374 / (Real.pi * ρ ^ 6) := by positivity
  by_cases hcase : (τ : ℝ) ≤ Real.sqrt δ
  · refine (lintegral_sq_compK2_sub_le_exit hU hD hDU hρ hxD hcD hτ).trans ?_
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
    rw [h4, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : (τ : ℝ) ^ 2 ≤ δ := by
      calc (τ : ℝ) ^ 2 ≤ Real.sqrt δ ^ 2 := pow_le_pow_left₀ hτ'.le hcase 2
        _ = δ := Real.sq_sqrt hδ0.le
    calc 4 * eB ρ τ ≤ 4 * (4374 / (Real.pi * ρ ^ 6) * (τ : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (eB_le_sq hρ hτ') (by norm_num)
      _ ≤ 4 * (4374 / (Real.pi * ρ ^ 6) * δ) := by gcongr
      _ ≤ (3 / (4 * Real.pi) + 87480 / (Real.pi * ρ ^ 6)) * δ := by
          have : 0 ≤ 3 / (4 * Real.pi) * δ := by positivity
          have e : 87480 / (Real.pi * ρ ^ 6) = 20 * (4374 / (Real.pi * ρ ^ 6)) := by ring
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
    have h := lintegral_sq_compK2_sub_le hU hD hDU hτ₁0 hτ₂0 x c
    rw [hsum] at h
    have hU1 : Metric.ball x ρ ⊆ U := hxD.trans hDU
    have hU2 : Metric.ball c ρ ⊆ U := hcD.trans hDU
    have hA := lintegral_sq_killedHeat_sub_le hU hρ hU1 hU2 hτ₁0
    have hB := lintegral_sq_compK2_sub_le_exit hU hD hDU hρ hxD hcD hτ₁0
    refine h.trans ?_
    refine (add_le_add (mul_le_mul_of_nonneg_left hA zero_le)
      (mul_le_mul_of_nonneg_left hB zero_le)).trans ?_
    have hsq : (τ₁ : ℝ) ^ 2 = δ := by rw [hτ₁v, Real.sq_sqrt hδ0.le]
    have hE0 : 0 ≤ eB ρ τ₁ := eB_nonneg ρ (NNReal.coe_nonneg τ₁)
    have hq0 : 0 ≤ ‖x - c‖ ^ 2 / (8 * Real.pi * (τ₁ : ℝ) ^ 2) := by positivity
    have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    have e3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
    have e4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
    have e6 : (6 : ℝ≥0∞) = ENNReal.ofReal 6 := by simp
    rw [e2, e3, e4, e6, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hE := eB_le_sq hρ (pos_of_ne hτ₁0)
    rw [hsq] at hE
    rw [← hδ, hsq]
    have e1 : 2 * (3 * (δ ^ 2 / (8 * Real.pi * δ))) = 3 / (4 * Real.pi) * δ := by
      field_simp; ring
    have e : 87480 / (Real.pi * ρ ^ 6) = 20 * (4374 / (Real.pi * ρ ^ 6)) := by ring
    rw [add_mul, e]
    nlinarith

end DG
end LQGMetric
