/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppA1SP at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppASP2

/-!
# Ding–Gwynne Lemma A.1: start-point regularity of `p_U − p_D` (task P2-DG3B)

DG (`metric-comparison-final.tex`, proof of Lemma A.1, DG:2141–2232): the kernel of
`f_t(z) = h^U_{t,1}(z) − ĥ^tr_t(z)` is `q_s(z, ·) = p_U(s/2; z, ·) − p_{B_{1/10}(z)}(s/2; z, ·)`.
This file generalizes `AppASP`/`AppASP2` from `U = ℂ` to an open `U ⊇ D`:
`a_x(τ) = p_U(τ; x, ·) − p_D(τ; x, ·)` (`compK2`).

* `compK2_split` — Chapman–Kolmogorov splitting (as `compK_split`, with `p_U` for `p`);
* `lintegral_sq_compK2_sub_le_unif` — if `B(x,ρ), B(c,ρ) ⊆ D ⊆ U` then for all `τ > 0`,
  `‖a_x(τ) − a_c(τ)‖₂² ≤ (3/(4π) + 87480/(πρ⁶)) |x − c|`.

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

/-- `a_x(τ)(w) = p_U(τ; x, w) − p_D(τ; x, w)`. -/
def compK2 (U D : Set ℂ) (τ : ℝ≥0) (x w : ℂ) : ℝ := killedHeat U τ x w - killedHeat D τ x w

lemma compK2_nonneg {U D : Set ℂ} (hDU : D ⊆ U) (τ : ℝ≥0) (x w : ℂ) : 0 ≤ compK2 U D τ x w :=
  sub_nonneg.2 (killedHeat_mono hDU _ _ _)

lemma compK2_le_compK (U D : Set ℂ) (τ : ℝ≥0) (x w : ℂ) : compK2 U D τ x w ≤ compK D τ x w :=
  sub_le_sub_right (killedHeat_le_heatKernel _ _ _ _) _

lemma compK2_le (U D : Set ℂ) (τ : ℝ≥0) (x w : ℂ) : compK2 U D τ x w ≤ heatKernel τ x w :=
  (compK2_le_compK U D τ x w).trans (compK_le _ _ _ _)

lemma measurable_compK2_right {U D : Set ℂ} (hU : IsOpen U) (hD : IsOpen D) {τ : ℝ≥0}
    (hτ : τ ≠ 0) (x : ℂ) : Measurable fun w => compK2 U D τ x w :=
  (measurable_killedHeat_right hU hτ x).sub (measurable_killedHeat_right hD hτ x)

lemma measurable_compK2_left {U D : Set ℂ} (hU : IsOpen U) (hD : IsOpen D) {τ : ℝ≥0}
    (hτ : τ ≠ 0) (w : ℂ) : Measurable fun x => compK2 U D τ x w :=
  (measurable_killedHeat_left hU hτ w).sub (measurable_killedHeat_left hD hτ w)

/-- Chapman–Kolmogorov splitting of `a_x`. -/
theorem compK2_split {U D : Set ℂ} (hU : IsOpen U) (hD : IsOpen D) (hDU : D ⊆ U)
    {τ₁ τ₂ : ℝ≥0} (h₁ : τ₁ ≠ 0) (h₂ : τ₂ ≠ 0) (x w : ℂ) :
    compK2 U D (τ₁ + τ₂) x w = (∫ y, killedHeat U τ₁ x y * compK2 U D τ₂ y w) +
      ∫ y, compK2 U D τ₁ x y * killedHeat D τ₂ y w := by
  have ck1 := killedHeat_chapmanKolmogorov hU h₁ h₂ x w
  have ck2 := killedHeat_chapmanKolmogorov hD h₁ h₂ x w
  have hh0 : ∀ (t : ℝ≥0) (a b : ℂ), 0 ≤ heatKernel t a b := fun t a b => heatKernel_nonneg' t a b
  have iK : ∀ {A B : Set ℂ}, IsOpen A → IsOpen B →
      Integrable fun y => killedHeat A τ₁ x y * killedHeat B τ₂ y w := by
    intro A B hA hB
    refine integrable_of_le_heat_mul h₁ h₂ x w ((measurable_killedHeat_right hA h₁ x).mul
      (measurable_killedHeat_left hB h₂ w)) fun y => ?_
    rw [abs_of_nonneg (mul_nonneg (killedHeat_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _))]
    exact mul_le_mul (killedHeat_le_heatKernel _ _ _ _) (killedHeat_le_heatKernel _ _ _ _)
      (killedHeat_nonneg _ _ _ _) (hh0 _ _ _)
  unfold compK2
  simp_rw [mul_sub, sub_mul]
  rw [integral_sub (iK hU hU) (iK hU hD), integral_sub (iK hU hD) (iK hD hD), ck1, ck2]
  ring

/-- `‖p_U(τ; x, ·) − p_U(τ; c, ·)‖₂² ≤ 3|x − c|²/(8πτ²) + 6 eB ρ τ` if `B(x,ρ), B(c,ρ) ⊆ U`. -/
lemma lintegral_sq_killedHeat_sub_le {U : Set ℂ} (hU : IsOpen U) {x c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hxU : Metric.ball x ρ ⊆ U) (hcU : Metric.ball c ρ ⊆ U) {τ : ℝ≥0} (hτ : τ ≠ 0) :
    ∫⁻ y, ENNReal.ofReal ((killedHeat U τ x y - killedHeat U τ c y) ^ 2) ≤
      3 * ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (τ : ℝ) ^ 2)) +
        6 * ENNReal.ofReal (eB ρ τ) := by
  have h3 : ∀ a b d : ℝ, ENNReal.ofReal ((a - b + d) ^ 2) ≤
      3 * ENNReal.ofReal (a ^ 2) + 3 * ENNReal.ofReal (b ^ 2) + 3 * ENNReal.ofReal (d ^ 2) := by
    intro a b d
    have e3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
    rw [e3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - d), sq_nonneg (b + d)]
  have hpt : ∀ y, killedHeat U τ x y - killedHeat U τ c y =
      (heatKernel τ x y - heatKernel τ c y) - compK U τ x y + compK U τ c y := by
    intro y; unfold compK; ring
  have hm1 : Measurable fun y => (heatKernel τ x y - heatKernel τ c y) :=
    (measurable_heatKernel_right _ x).sub (measurable_heatKernel_right _ c)
  have hm2 := measurable_compK_right hU hτ x
  calc ∫⁻ y, ENNReal.ofReal ((killedHeat U τ x y - killedHeat U τ c y) ^ 2)
      ≤ ∫⁻ y, (3 * ENNReal.ofReal ((heatKernel τ x y - heatKernel τ c y) ^ 2) +
          3 * ENNReal.ofReal (compK U τ x y ^ 2) + 3 * ENNReal.ofReal (compK U τ c y ^ 2)) :=
        lintegral_mono fun y => by rw [hpt y]; exact h3 _ _ _
    _ = 3 * (∫⁻ y, ENNReal.ofReal ((heatKernel τ x y - heatKernel τ c y) ^ 2)) +
          3 * (∫⁻ y, ENNReal.ofReal (compK U τ x y ^ 2)) +
          3 * ∫⁻ y, ENNReal.ofReal (compK U τ c y ^ 2) := by
        have hA : AEMeasurable (fun y => 3 * ENNReal.ofReal ((heatKernel τ x y -
            heatKernel τ c y) ^ 2) + 3 * ENNReal.ofReal (compK U τ x y ^ 2)) volume :=
          (((hm1.pow_const 2).ennreal_ofReal.const_mul 3).add
            ((hm2.pow_const 2).ennreal_ofReal.const_mul 3)).aemeasurable
        rw [lintegral_add_left' hA,
          lintegral_add_left' (((hm1.pow_const 2).ennreal_ofReal.const_mul 3)).aemeasurable,
          lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp),
          lintegral_const_mul' _ _ (by simp)]
    _ ≤ 3 * ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (τ : ℝ) ^ 2)) +
          3 * ENNReal.ofReal (eB ρ τ) + 3 * ENNReal.ofReal (eB ρ τ) := by
        gcongr
        · exact lintegral_sq_heat_sub_le hτ x c
        · exact lintegral_sq_compK_le hU hρ hxU hτ
        · exact lintegral_sq_compK_le hU hρ hcU hτ
    _ = _ := by ring

/-- `‖a_x(τ)‖₂² ≤ eB ρ τ` if `B(x, ρ) ⊆ D ⊆ U`. -/
lemma lintegral_sq_compK2_le {U D : Set ℂ} (hD : IsOpen D) (hDU : D ⊆ U) {x : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hxD : Metric.ball x ρ ⊆ D) {τ : ℝ≥0} (hτ : τ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal (compK2 U D τ x w ^ 2) ≤ ENNReal.ofReal (eB ρ τ) :=
  (lintegral_mono fun w => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (compK2_nonneg hDU _ _ _)
    (compK2_le_compK U D τ x w) 2)).trans (lintegral_sq_compK_le hD hρ hxD hτ)

end DG
end LQGMetric
