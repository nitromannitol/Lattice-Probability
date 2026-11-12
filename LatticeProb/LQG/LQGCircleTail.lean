import Mathlib
import LatticeProb.LQG.GMCCircleLaw
import LatticeProb.Gauss.GaussianBorelCantelli

/-! # Gaussian tail of a circle average of the whole-plane GFF

For the whole-plane GFF `h` normalised by `h_1(0) = 0` and a point `z` with `‖z‖ ≤ 2`, the circle average `h_r(z)` of a
small radius `r ≤ 1` is a centred Gaussian whose variance is at most `log (1/r) + 2 log 3`
(`Var h_r(z) = 2 · avg_{∂B_r(z)} log max(|·|, 1) - log r`). Hence the lower tail of `h_r(z)` at the level
`-τ log (1/r)` is of order `r^{τ²/2}`:
  `P(h_r(z) ≤ -τ log (1/r)) ≤ 2 · 3^{τ²} · r^{τ²/2}`.

Main results:
* `IsWholePlaneGFF.variance_circle_le`: the variance bound.
* `IsWholePlaneGFF.hasLaw_circle`: the law `N(0, Var h_r(z))`.
* `IsWholePlaneGFF.measure_circle_le_neg`: the lower tail estimate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Variance bound for circle averages.** For `0 < r ≤ 1` and `‖z‖ ≤ 2`,
`Var h_r(z) ≤ log (1/r) + 2 log 3`. -/
theorem IsWholePlaneGFF.variance_circle_le (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    Var[fun ω => hcirc ω r z; P] ≤ -Real.log r + 2 * Real.log 3 := by
  have hP := hh.isProbabilityMeasure
  rw [← covariance_self (hh.hasGaussianLaw_circle hr z).aemeasurable,
    hh.covariance_circle_circle hr hr, wholePlaneGFFCov_circle_circle_eq hr,
    circlePairPotential_self_center hr.le, max_self]
  have hA : Real.circleAverage logMaxAbs z r ≤ Real.log 3 := by
    refine Real.circleAverage_mono_on_of_le_circle
      logMaxAbs_continuous.continuousOn.circleIntegrable' fun x hx => ?_
    have hx' : ‖x - z‖ = r := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
    have h3 : ‖x‖ ≤ 3 := by linarith [norm_sub_norm_le x z]
    unfold logMaxAbs
    exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
      (max_le h3 (by norm_num))
  linarith

/-- **Law of a circle average.** `h_r(z) ∼ N(0, Var h_r(z))`. -/
theorem IsWholePlaneGFF.hasLaw_circle (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r)
    (z : ℂ) :
    HasLaw (fun ω => hcirc ω r z) (gaussianReal 0 (Var[fun ω => hcirc ω r z; P]).toNNReal) P := by
  have hG := hh.hasGaussianLaw_circle hr z
  have hmean : ∫ ω, hcirc ω r z ∂P = 0 := hh.integral_eq_zero (.circle r z) hr
  exact ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean]⟩

/-- **Lower tail of a circle average.** For `0 < r ≤ 1`, `‖z‖ ≤ 2` and `τ ≥ 0`,
`P(h_r(z) ≤ -τ log (1/r)) ≤ 2 · 3^{τ²} · r^{τ²/2}`. -/
theorem IsWholePlaneGFF.measure_circle_le_neg (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 2) {τ : ℝ} (hτ : 0 ≤ τ) :
    P {ω | hcirc ω r z ≤ -(τ * -Real.log r)} ≤
      ENNReal.ofReal (2 * (3 : ℝ) ^ (τ ^ 2) * r ^ (τ ^ 2 / 2)) := by
  have hP := hh.isProbabilityMeasure
  have hL : 0 ≤ -Real.log r := neg_nonneg.2 (Real.log_nonpos hr.le hr1)
  have hV := hh.variance_circle_le hr hr1 hz
  have hvar0 : 0 ≤ Var[fun ω => hcirc ω r z; P] := variance_nonneg _ _
  have hlaw := hh.hasLaw_circle hr z
  have hsub : {ω | hcirc ω r z ≤ -(τ * -Real.log r)} ⊆ {ω | τ * -Real.log r ≤ |hcirc ω r z|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith [neg_le_abs (hcirc ω r z)]
  have hcher := GaussBC.measureReal_le_abs_le hlaw (a := τ * -Real.log r) hτ
  rw [Real.coe_toNNReal _ hvar0] at hcher
  have hexp : Real.exp (-τ * (τ * -Real.log r) + Var[fun ω => hcirc ω r z; P] * τ ^ 2 / 2) ≤
      (3 : ℝ) ^ (τ ^ 2) * r ^ (τ ^ 2 / 2) := by
    have h1 : -τ * (τ * -Real.log r) + Var[fun ω => hcirc ω r z; P] * τ ^ 2 / 2 ≤
        Real.log 3 * τ ^ 2 + Real.log r * (τ ^ 2 / 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hV (sq_nonneg τ)]
    calc _ ≤ Real.exp (Real.log 3 * τ ^ 2 + Real.log r * (τ ^ 2 / 2)) := Real.exp_le_exp.2 h1
      _ = _ := by
        rw [Real.exp_add, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
          ← Real.rpow_def_of_pos hr]
  calc P {ω | hcirc ω r z ≤ -(τ * -Real.log r)}
      ≤ P {ω | τ * -Real.log r ≤ |hcirc ω r z|} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | τ * -Real.log r ≤ |hcirc ω r z|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * (3 : ℝ) ^ (τ ^ 2) * r ^ (τ ^ 2 / 2)) := by
        refine ENNReal.ofReal_le_ofReal (hcher.trans ?_)
        calc _ ≤ 2 * ((3 : ℝ) ^ (τ ^ 2) * r ^ (τ ^ 2 / 2)) := by gcongr
          _ = _ := by ring

end LatticeProb.Gauss
