/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.AppA1Tail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.AppA1SP2

/-!
DG (`metric-comparison-final.tex`, DG:2144–2162): `h^U = h^U_{1,∞} + lim_{t→0} h^U_{t,1}` and
`(h^U − ĥ^tr)|_K = h^U_{1,∞} + f`, with `h^U_{1,∞}(z) = √π ∫_1^∞ ∫ p_U(s/2; z, w) W(dw, ds)`
("easily checked using the Kolmogorov continuity criterion", DG:2145). The kernel increments:

* `lintegral_killedHeat_right_le` — `∫ p_U(σ; u, w) dw ≤ 2R²/σ` for `U ⊆ B(c, R)`
  (`bridgeStay_le_of_subset_ball`);
* `lintegral_sq_integral_le_scaled` — Schur's test with constant `A`;
* `lintegral_sq_killedHeat_sub_tail_le` — for `τ = σ + 1/4`, `σ > 0`, `B(x, ρ), B(c, ρ) ⊆ U`:
  `‖p_U(τ; x, ·) − p_U(τ; c, ·)‖₂² ≤ (2R²/σ)² (2|x−c|²/(8π/16) + 2C(ρ)|x − c|)`
  (Chapman–Kolmogorov at time `1/4`, then `p_U = p − (p − p_U)` and `AppASP2`).
Own argument (DEVIATIONS DG3B-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat

/-- `∫ p_U(σ; u, w) dw ≤ 2R²/σ` for `U ⊆ B(c, R)`. -/
lemma lintegral_killedHeat_right_le {U : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ Metric.ball c R) {σ : ℝ≥0} (hσ : σ ≠ 0) (u : ℂ) :
    ∫⁻ w, ENNReal.ofReal (killedHeat U σ u w) ≤ ENNReal.ofReal (2 * R ^ 2 / σ) := by
  have hσ' := pos_of_ne hσ
  set a : ℝ≥0 := σ / 2
  have haa : a + a = σ := add_halves σ
  have ha : a ≠ 0 := div_ne_zero hσ two_ne_zero
  have hq : ∀ w, bridgeStay U σ u w ≤ 2 * R ^ 2 / σ := by
    intro w
    have h := bridgeStay_le_of_subset_ball hR hUR ha u w
    rw [haa] at h
    refine h.trans (le_of_eq ?_)
    simp only [a, NNReal.coe_div, NNReal.coe_ofNat]
    field_simp
  calc ∫⁻ w, ENNReal.ofReal (killedHeat U σ u w)
      ≤ ∫⁻ w, ENNReal.ofReal (2 * R ^ 2 / σ) * ENNReal.ofReal (heatKernel σ u w) := by
        refine lintegral_mono fun w => ?_
        rw [← ENNReal.ofReal_mul (by positivity), killedHeat, mul_comm]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hq w) (heatKernel_nonneg' _ _ _))
    _ = ENNReal.ofReal (2 * R ^ 2 / σ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          GFFExist.lintegral_ofReal_heatKernel hσ' u, mul_one]

/-- Schur's test with constant: if `|G| ≤ K`, `∫ K dy ≤ A`, `∫ K dw ≤ A` (`A > 0`), then
`∫ (∫ f G dy)² dw ≤ A² ∫ f²`. -/
lemma lintegral_sq_integral_le_scaled {f : ℂ → ℝ} {G K : ℂ → ℂ → ℝ} (hf : Measurable f)
    (hK : Measurable (Function.uncurry K)) (hGK : ∀ y w, |G y w| ≤ K y w) {A : ℝ} (hA : 0 < A)
    (hK1 : ∀ w, ∫⁻ y, ENNReal.ofReal (K y w) ≤ ENNReal.ofReal A)
    (hK2 : ∀ y, ∫⁻ w, ENNReal.ofReal (K y w) ≤ ENNReal.ofReal A) :
    ∫⁻ w, ENNReal.ofReal ((∫ y, f y * G y w) ^ 2) ≤
      ENNReal.ofReal (A ^ 2) * ∫⁻ y, ENNReal.ofReal (f y ^ 2) := by
  have hscale : ∀ {g : ℂ → ℝ}, ∫⁻ y, ENNReal.ofReal (g y / A) =
      ENNReal.ofReal A⁻¹ * ∫⁻ y, ENNReal.ofReal (g y) := by
    intro g
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by positivity)]
  have hinvA : ∀ x : ℝ≥0∞, x ≤ ENNReal.ofReal A → ENNReal.ofReal A⁻¹ * x ≤ 1 := by
    intro x hx
    calc ENNReal.ofReal A⁻¹ * x ≤ ENNReal.ofReal A⁻¹ * ENNReal.ofReal A :=
          mul_le_mul_of_nonneg_left hx zero_le
      _ = 1 := by rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hA.ne',
          ENNReal.ofReal_one]
  have h := lintegral_sq_integral_le (f := f) (G := fun y w => G y w / A)
    (K := fun y w => K y w / A) hf (hK.div_const A)
    (fun y w => by rw [abs_div, abs_of_pos hA]; exact div_le_div_of_nonneg_right (hGK y w) hA.le)
    (fun w => by rw [hscale]; exact hinvA _ (hK1 w))
    (fun y => by rw [hscale]; exact hinvA _ (hK2 y))
  have e : ∀ w, (∫ y, f y * (G y w / A)) ^ 2 = A⁻¹ ^ 2 * (∫ y, f y * G y w) ^ 2 := by
    intro w
    simp_rw [mul_div_assoc', div_eq_mul_inv]
    rw [integral_mul_const]
    ring
  simp_rw [e, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ A⁻¹ ^ 2)] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  calc ∫⁻ w, ENNReal.ofReal ((∫ y, f y * G y w) ^ 2)
      = ENNReal.ofReal (A ^ 2) * (ENNReal.ofReal (A⁻¹ ^ 2) *
          ∫⁻ w, ENNReal.ofReal ((∫ y, f y * G y w) ^ 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_pow,
          mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h zero_le

/-- **Tail kernel increments**: for `U ⊆ B(c₀, R)`, `B(x, ρ), B(c, ρ) ⊆ U`, `q, σ > 0`:
`‖p_U(q+σ; x, ·) − p_U(q+σ; c, ·)‖₂² ≤ (2R²/σ)² (2|x−c|²/(8πq²) + 2 C(ρ)|x − c|)`,
`C(ρ) = 1/(4π) + 34992/(πρ⁶)`. -/
theorem lintegral_sq_killedHeat_sub_tail_le {U : Set ℂ} (hU : IsOpen U) {c₀ : ℂ} {R : ℝ}
    (hR : 0 < R) (hUR : U ⊆ Metric.ball c₀ R) {x c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hxU : Metric.ball x ρ ⊆ U) (hcU : Metric.ball c ρ ⊆ U) {q σ : ℝ≥0} (hq : q ≠ 0)
    (hσ : σ ≠ 0) :
    ∫⁻ w, ENNReal.ofReal ((killedHeat U (q + σ) x w - killedHeat U (q + σ) c w) ^ 2) ≤
      ENNReal.ofReal ((2 * R ^ 2 / σ) ^ 2) *
        (2 * ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (q : ℝ) ^ 2)) +
          2 * ENNReal.ofReal ((1 / (4 * Real.pi) + 34992 / (Real.pi * ρ ^ 6)) * ‖x - c‖)) := by
  have hσ' := pos_of_ne hσ
  have hA : 0 < 2 * R ^ 2 / (σ : ℝ) := by positivity
  have hh0 : ∀ (t : ℝ≥0) (a b : ℂ), 0 ≤ heatKernel t a b := fun t a b => heatKernel_nonneg' t a b
  have iK : ∀ u w, Integrable fun y => killedHeat U q u y * killedHeat U σ y w := by
    intro u w
    refine integrable_of_le_heat_mul hq hσ u w ((measurable_killedHeat_right hU hq u).mul
      (measurable_killedHeat_left hU hσ w)) fun y => ?_
    rw [abs_of_nonneg (mul_nonneg (killedHeat_nonneg _ _ _ _) (killedHeat_nonneg _ _ _ _))]
    exact mul_le_mul (killedHeat_le_heatKernel _ _ _ _) (killedHeat_le_heatKernel _ _ _ _)
      (killedHeat_nonneg _ _ _ _) (hh0 _ _ _)
  have hpt : ∀ w, killedHeat U (q + σ) x w - killedHeat U (q + σ) c w =
      ∫ y, (killedHeat U q x y - killedHeat U q c y) * killedHeat U σ y w := by
    intro w
    rw [killedHeat_chapmanKolmogorov hU hq hσ x w, killedHeat_chapmanKolmogorov hU hq hσ c w,
      ← integral_sub (iK x w) (iK c w)]
    congr 1; funext y; ring
  have hfm : Measurable fun y => killedHeat U q x y - killedHeat U q c y :=
    (measurable_killedHeat_right hU hq x).sub (measurable_killedHeat_right hU hq c)
  have hS := lintegral_sq_integral_le_scaled (f := fun y => killedHeat U q x y - killedHeat U q c y)
    (G := fun y w => killedHeat U σ y w) (K := fun y w => killedHeat U σ y w) hfm
    (measurable_killedHeat_uncurry hU σ)
    (fun y w => le_of_eq (abs_of_nonneg (killedHeat_nonneg _ _ _ _))) hA
    (fun w => (le_of_eq (lintegral_congr fun y => by rw [killedHeat_symm hU σ y w])).trans
      (lintegral_killedHeat_right_le hR.le hUR hσ w))
    (fun y => lintegral_killedHeat_right_le hR.le hUR hσ y)
  have hm1 : Measurable fun y => heatKernel q x y - heatKernel q c y :=
    (measurable_heatKernel_right _ x).sub (measurable_heatKernel_right _ c)
  have hf2 : ∫⁻ y, ENNReal.ofReal ((killedHeat U q x y - killedHeat U q c y) ^ 2) ≤
      2 * ENNReal.ofReal (‖x - c‖ ^ 2 / (8 * Real.pi * (q : ℝ) ^ 2)) +
        2 * ENNReal.ofReal ((1 / (4 * Real.pi) + 34992 / (Real.pi * ρ ^ 6)) * ‖x - c‖) := by
    have e : ∀ y, killedHeat U q x y - killedHeat U q c y =
        (heatKernel q x y - heatKernel q c y) - (compK U q x y - compK U q c y) := by
      intro y; unfold compK; ring
    calc ∫⁻ y, ENNReal.ofReal ((killedHeat U q x y - killedHeat U q c y) ^ 2)
        ≤ ∫⁻ y, (2 * ENNReal.ofReal ((heatKernel q x y - heatKernel q c y) ^ 2) +
            2 * ENNReal.ofReal ((compK U q x y - compK U q c y) ^ 2)) :=
          lintegral_mono fun y => by rw [e y]; exact ofReal_sq_sub_le _ _
      _ = 2 * (∫⁻ y, ENNReal.ofReal ((heatKernel q x y - heatKernel q c y) ^ 2)) +
            2 * ∫⁻ y, ENNReal.ofReal ((compK U q x y - compK U q c y) ^ 2) := by
          rw [lintegral_add_left' (((hm1.pow_const 2).ennreal_ofReal).const_mul 2).aemeasurable,
            lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
      _ ≤ _ := by
          gcongr
          · exact lintegral_sq_heat_sub_le hq x c
          · exact lintegral_sq_compK_sub_le_unif hU hρ hxU hcU hq
  calc ∫⁻ w, ENNReal.ofReal ((killedHeat U (q + σ) x w - killedHeat U (q + σ) c w) ^ 2)
      = ∫⁻ w, ENNReal.ofReal ((∫ y, (killedHeat U q x y - killedHeat U q c y) *
          killedHeat U σ y w) ^ 2) := lintegral_congr fun w => by rw [hpt w]
    _ ≤ ENNReal.ofReal ((2 * R ^ 2 / σ) ^ 2) *
          ∫⁻ y, ENNReal.ofReal ((killedHeat U q x y - killedHeat U q c y) ^ 2) := hS
    _ ≤ _ := mul_le_mul_of_nonneg_left hf2 zero_le

end DG
end LQGMetric
