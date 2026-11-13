import Mathlib
import LatticeProb.LQG.MarkedRootingCircle
import LatticeProb.LQG.WholePlaneCircleTilt

/-!
# The marked rooting identity with an exponential circle-average weight

For the whole-plane Gaussian free field `h` (vanishing average over the unit circle) and its `γ`-Liouville measure
`μ`, test functions `ψ_i` supported in the unit disk and a radius `0 < ρ ≤ 1`, the marked rooting identity with the
circle average `h_ρ(0)` as an extra mark (the Palm form of the Gaussian multiplicative chaos) is combined with the
Cameron–Martin tilt by `exp (-γ h_ρ(0))`: the weight `exp (-γ h_ρ(0))` disappears from the expectation and is
replaced by the deterministic factor `exp (γ² (-log ρ) / 2 + γ² log max(ρ, |w|))` and a deterministic shift of the
pairings.

* `IsWholePlaneGFF.lintegral_lqgMeasure_marked_tilt`: the identity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Marked rooting identity with the weight `exp (-γ h_ρ(0))`.** Let `X = ((h, ψ_i))_i`, with `ψ_i` supported in
the unit disk, `0 < ρ ≤ 1` and `F ≥ 0` measurable. Then
`E [∫_{𝔻} e^{-γ h_ρ(0)} F (w, X) dμ (w)] =
  ∫_{𝔻} e^{γ² (-log ρ) / 2 + γ² log max(ρ, |w|)} E [F (w, X + γ s(w))] dw`,
where `s_i(w) = ∫ ψ_i(x) Cov (h(x), h(w)) dx - ∫ ψ_i(x) (-log max(ρ, |x|)) dx`. -/
theorem lintegral_lqgMeasure_marked_tilt (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ) {m : ℕ}
    {ψ : Fin m → ℂ → ℝ} (hψ : ∀ i, IsTestFunction Set.univ (ψ i)) (hψs : ∀ i x, ψ i x ≠ 0 → ‖x‖ < 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {F : ℂ × (Fin m → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, ∫⁻ w in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (Real.exp (-γ * hcirc ω ρ 0)) * F (w, fun i => hC ω (ψ i)) ∂(μ ω) ∂P =
      ∫⁻ w in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (Real.exp (γ ^ 2 * (-Real.log ρ) / 2 + γ ^ 2 * Real.log (max ρ ‖w‖))) *
          ∫⁻ ω, F (w, fun i => hC ω (ψ i) + γ * ((∫ x, ψ i x * wholePlaneCov x w) -
            ∫ x, ψ i x * -Real.log (max ρ ‖x‖))) ∂P := by
  have hfm : Measurable fun q : (ℂ × (Fin m → ℝ)) × ℝ =>
      ENNReal.ofReal (Real.exp (-γ * q.2)) * F q.1 :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_snd.const_mul _))).mul
      (hF.comp measurable_fst)
  have h := (hh.lintegral_lqgMeasure_marked_circle_fun_eq hγ0 hγ2 hμ hψ hρ hfm).2
  refine h.trans ?_
  refine setLIntegral_congr_fun measurableSet_ball fun w hw => ?_
  have hw1 : ‖w‖ < 1 := by simpa using hw
  have hcτ : Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ = -Real.log (max ρ ‖w‖) := by
    rw [circleAverage_wholePlaneCov_eq hρ 0 w]
    have hA : Real.circleAverage wholePlaneNormalization 0 ρ = 0 :=
      circleAverage_log_max_norm_one_of_le_one hρ hρ1
    have hN : wholePlaneNormalization w = 0 := by
      simp [wholePlaneNormalization, max_eq_right hw1.le]
    rw [hA, hN, zero_sub, norm_neg]
    ring
  set Φ : (Fin m → ℝ) → ℝ≥0∞ :=
    fun x => F (w, fun i => x i + γ * ∫ x', ψ i x' * wholePlaneCov x' w) with hΦdef
  have hΦm : Measurable Φ :=
    hF.comp (measurable_const.prodMk (measurable_pi_iff.2 fun i =>
      (measurable_pi_apply i).add_const _))
  have hsplit : ∀ ω, ENNReal.ofReal (Real.exp (-γ * (hcirc ω ρ 0 +
        γ * Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ))) *
      F (w, fun i => hC ω (ψ i) + γ * ∫ x, ψ i x * wholePlaneCov x w) =
      ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ)) *
        (ENNReal.ofReal (Real.exp (-γ * hcirc ω ρ 0)) * Φ (fun i => hC ω (ψ i))) := fun ω => by
    have h1 : -γ * (hcirc ω ρ 0 + γ * Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ) =
        -γ ^ 2 * Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ + -γ * hcirc ω ρ 0 := by ring
    rw [h1, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
  have hcov : ∀ i, wholePlaneGFFCov (.pairing (ψ i)) (.circle ρ 0) =
      ∫ x, ψ i x * -Real.log (max ρ ‖x‖) := fun i =>
    wholePlaneGFFCov_pairing_circle_of_ball (ψ i) hρ hρ1 (hψs i)
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * (hcirc ω ρ 0 +
        γ * Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ))) *
      F (w, fun i => hC ω (ψ i) + γ * ∫ x, ψ i x * wholePlaneCov x w) ∂P
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (-γ ^ 2 *
          Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ)) *
        (ENNReal.ofReal (Real.exp (-γ * hcirc ω ρ 0)) * Φ (fun i => hC ω (ψ i))) ∂P :=
        lintegral_congr hsplit
    _ = ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ)) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * hcirc ω ρ 0)) * Φ (fun i => hC ω (ψ i)) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.circleAverage (fun y => wholePlaneCov w y) 0 ρ)) *
        (ENNReal.ofReal (Real.exp ((-γ) ^ 2 *
          wholePlaneGFFCov (.circle ρ 0) (.circle ρ 0) / 2)) *
          ∫⁻ ω, Φ (fun i => hC ω (ψ i) +
            (-γ) * wholePlaneGFFCov (.pairing (ψ i)) (.circle ρ 0)) ∂P) := by
        rw [hh.lintegral_exp_circle_tilt hψ hρ (-γ) hΦm]
    _ = _ := by
        rw [wholePlaneGFFCov_circle_circle_of_le_one hρ hρ1, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 1
        · congr 2
          rw [hcτ]
          ring
        · refine lintegral_congr fun ω => ?_
          simp only [hΦdef, hcov]
          exact congrArg (fun x => F (w, x)) (funext fun i => by ring)

end IsWholePlaneGFF

end LatticeProb.Gauss
