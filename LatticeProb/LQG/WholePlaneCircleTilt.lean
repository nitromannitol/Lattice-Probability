import Mathlib
import LatticeProb.Gauss.GaussianTilt
import LatticeProb.Gauss.GFFIncrementBound
import LatticeProb.Gauss.CircleAverageApprox2
import LatticeProb.LQG.MarkedRootingCov

/-!
# Exponential tilt of a whole-plane GFF by a circle average

For the whole-plane Gaussian free field `h` normalized to have vanishing average over the unit circle, the
exponential `exp (a h_ρ(0))` of a circle average acts on finite families of pairings `(h, ψ_i)` as a Cameron–Martin
shift (Girsanov): for every measurable `Φ ≥ 0`,
`E [exp (a h_ρ(0)) Φ ((h, ψ_i)_i)] = exp (a² Var (h_ρ(0)) / 2) · E [Φ ((h, ψ_i) + a Cov ((h, ψ_i), h_ρ(0)))_i]`.

* `IsWholePlaneGFF.lintegral_exp_circle_tilt`: the tilt identity.
* `wholePlaneGFFCov_circle_circle_of_le_one`: `Var (h_ρ(0)) = - log ρ` for `0 < ρ ≤ 1`.
* `wholePlaneGFFCov_pairing_circle_of_ball`: for `0 < ρ ≤ 1` and `ψ` supported in the unit disk,
  `Cov ((h, ψ), h_ρ(0)) = ∫ ψ(x) (- log max(ρ, |x|)) dx`.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace LatticeProb.Gauss

/-- The observable attached to an index of the tilted family: the circle average `h_ρ(0)` for `none` and the pairing
with `ψ i` for `some i`. -/
def tiltObs {m : ℕ} (ψ : Fin m → ℂ → ℝ) (ρ : ℝ) : Option (Fin m) → GFFObservable
  | none => .circle ρ 0
  | some i => .pairing (ψ i)

theorem tiltObs_isAdmissible {m : ℕ} {ψ : Fin m → ℂ → ℝ} (hψ : ∀ i, IsTestFunction Set.univ (ψ i))
    {ρ : ℝ} (hρ : 0 < ρ) (o : Option (Fin m)) : (tiltObs ψ ρ o).IsAdmissible := by
  cases o with
  | none => exact hρ
  | some i => exact hψ i

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Exponential tilt by a circle average.** For the whole-plane GFF, test functions `ψ_i`, a radius `ρ > 0`,
`a ∈ ℝ` and measurable `Φ : ℝⁿ → [0, ∞]`,
`E [e^{a h_ρ(0)} Φ ((h, ψ_i)_i)] = e^{a² Var (h_ρ(0)) / 2} E [Φ ((h, ψ_i) + a Cov ((h, ψ_i), h_ρ(0)))_i]`. -/
theorem lintegral_exp_circle_tilt (hh : IsWholePlaneGFF P hC hcirc) {m : ℕ} {ψ : Fin m → ℂ → ℝ}
    (hψ : ∀ i, IsTestFunction Set.univ (ψ i)) {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ)
    {Φ : (Fin m → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * hcirc ω ρ 0)) * Φ (fun i => hC ω (ψ i)) ∂P =
      ENNReal.ofReal (Real.exp (a ^ 2 * wholePlaneGFFCov (.circle ρ 0) (.circle ρ 0) / 2)) *
        ∫⁻ ω, Φ (fun i => hC ω (ψ i) + a * wholePlaneGFFCov (.pairing (ψ i)) (.circle ρ 0)) ∂P := by
  have hP := hh.isProbabilityMeasure
  set Y : Option (Fin m) → Ω → ℝ := fun o ω => (tiltObs ψ ρ o).eval (hC ω) (hcirc ω) with hY
  have hYG : IsGaussianProcess Y P :=
    hh.isGaussianProcess.comp_right fun o => (⟨tiltObs ψ ρ o, tiltObs_isAdmissible hψ hρ o⟩ :
      GFFObservable.Admissible)
  have hYm : ∀ o, Measurable (Y o) := fun o => by
    cases o with
    | none => exact hh.measurable_circle ρ 0 hρ
    | some i => exact hh.measurable_pairing _ (hψ i)
  have hcen : ∀ o, P[Y o] = 0 := fun o =>
    hh.integral_eq_zero _ (tiltObs_isAdmissible hψ hρ o)
  have hΦ' : Measurable fun y : Option (Fin m) → ℝ => Φ (fun i => y (some i)) :=
    hΦ.comp (measurable_pi_iff.2 fun i => measurable_pi_apply (some i))
  have key := LatticeProb.Gauss.lintegral_exp_mul_tilt hYG hYm hcen none a hΦ'
  have hvar : Var[Y none; P] = wholePlaneGFFCov (.circle ρ 0) (.circle ρ 0) := by
    rw [← covariance_self (hYm none).aemeasurable]
    exact hh.covariance_eq (.circle ρ 0) (.circle ρ 0) hρ hρ
  have hcov : ∀ i, cov[Y (some i), Y none; P] = wholePlaneGFFCov (.pairing (ψ i)) (.circle ρ 0) :=
    fun i => hh.covariance_eq (.pairing (ψ i)) (.circle ρ 0) (hψ i) hρ
  rw [hvar] at key
  simp only [hcov] at key
  have hsplit : ∀ ω, ENNReal.ofReal (Real.exp (a * hcirc ω ρ 0)) * Φ (fun i => hC ω (ψ i)) =
      ENNReal.ofReal (Real.exp (a ^ 2 * wholePlaneGFFCov (.circle ρ 0) (.circle ρ 0) / 2)) *
        (ENNReal.ofReal (Real.exp (a * Y none ω -
          a ^ 2 * wholePlaneGFFCov (.circle ρ 0) (.circle ρ 0) / 2)) *
          Φ (fun i => Y (some i) ω)) := fun ω => by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    simp only [hY, tiltObs, GFFObservable.eval]
    ring
  simp_rw [hsplit]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1

end IsWholePlaneGFF

/-- The circle average of `log max(|·|, 1)` over a circle about the origin of radius at most `1` vanishes. -/
theorem circleAverage_log_max_norm_one_of_le_one {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Real.circleAverage (fun x : ℂ => Real.log (max ‖x‖ 1)) 0 ρ = 0 := by
  have hcongr : Set.EqOn (fun x : ℂ => Real.log (max ‖x‖ 1)) (fun _ => (0 : ℝ))
      (Metric.sphere (0 : ℂ) |ρ|) := by
    intro y hy
    rw [mem_sphere_zero_iff_norm, abs_of_pos hρ] at hy
    simp only [hy, max_eq_right hρ1, Real.log_one]
  rw [Real.circleAverage_congr_sphere hcongr, Real.circleAverage_const]

/-- The variance of the circle average `h_ρ(0)` of the whole-plane GFF is `- log ρ` for `0 < ρ ≤ 1`. -/
theorem wholePlaneGFFCov_circle_circle_of_le_one {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    wholePlaneGFFCov (.circle ρ 0) (.circle ρ 0) = -Real.log ρ := by
  rw [wholePlaneGFFCov_circle_self_eq_sub_log hρ 0]
  have : Real.circleAverage logMaxAbs 0 ρ = 0 := circleAverage_log_max_norm_one_of_le_one hρ hρ1
  rw [this]
  ring

/-- For `0 < ρ ≤ 1` and `ψ` supported in the unit disk, `Cov ((h, ψ), h_ρ(0)) = ∫ ψ(x) (- log max(ρ, |x|)) dx`. -/
theorem wholePlaneGFFCov_pairing_circle_of_ball (ψ : ℂ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hψ : ∀ x, ψ x ≠ 0 → ‖x‖ < 1) :
    wholePlaneGFFCov (.pairing ψ) (.circle ρ 0) = ∫ x, ψ x * -Real.log (max ρ ‖x‖) := by
  rw [wholePlaneGFFCov_pairing_circle_eq ψ hρ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases h0 : ψ x = 0
  · simp [h0]
  · have hx := hψ x h0
    have hA : Real.circleAverage wholePlaneNormalization 0 ρ = 0 :=
      circleAverage_log_max_norm_one_of_le_one hρ hρ1
    have hN : wholePlaneNormalization x = 0 := by
      simp [wholePlaneNormalization, max_eq_right hx.le]
    show ψ x * (wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization 0 ρ -
      Real.log (max ρ ‖0 - x‖)) = _
    rw [hN, hA, zero_sub, norm_neg]
    ring

end LatticeProb.Gauss
