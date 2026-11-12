import Mathlib
import LatticeProb.LQG.GMCPointwiseMomentsLe

/-! # Independence of the coarse increment from the fine circle averages

For the whole-plane GFF `h`, `z ∈ ℂ` and `0 < r ≤ 1`, put `X = h_r(z) - h_1(z)`. The circle averages
`h'_ε(w) = h_{rε}(rw + z) - h_r(z)`, over the circles with `‖w‖ + ε ≤ 1` (i.e. the circles `∂B_{rε}(rw + z)` inside
the disc `B_r(z)`), are uncorrelated with `X`, hence independent of it, because the logarithmic kernel has constant
average over circles inside a disc (`circlePairPotential` of nested circles).

Main results:
* `circlePairPotential_nested`: the averaged potential of a circle inside `B_r(z)` over a circle of radius `t ≥ r`.
* `IsWholePlaneGFF.covariance_incr_fine_eq_zero`: `cov(h_r(z) - h_1(z), h_ρ(w) - h_r(z)) = 0` for `∂B_ρ(w) ⊆ B_r(z)`.
* `IsWholePlaneGFF.indepFun_incr_fine`: `h_r(z) - h_1(z)` is independent of the family `h'`.
-/

open MeasureTheory ProbabilityTheory Real Metric
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

/-- Averaging the potential of a circle `∂B_ρ(w) ⊆ B_r(z)` over a concentric circle `∂B_t(z)`, `t ≥ r`, gives
`log t`. -/
theorem circlePairPotential_nested {z w : ℂ} {r ρ t : ℝ} (ht : 0 < t) (hrt : r ≤ t) (hρ : 0 ≤ ρ)
    (hw : ‖w - z‖ + ρ ≤ r) : circlePairPotential z t w ρ = Real.log t := by
  have hwz : ‖z - w‖ ≤ t := by rw [norm_sub_rev]; linarith
  rw [circlePairPotential_of_ge ht (s := ρ) ?_, max_eq_left hwz]
  intro x hx
  have hx' : ‖x - z‖ = t := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos ht)
  have h1 := norm_sub_norm_le (x - z) (w - z)
  rw [sub_sub_sub_cancel_right] at h1
  linarith

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The coarse increment `h_r(z) - h_1(z)` is uncorrelated with every fine circle average
`h_ρ(w) - h_r(z)` whose circle `∂B_ρ(w)` lies in the disc `B_r(z)`. -/
theorem covariance_incr_fine_eq_zero (hh : IsWholePlaneGFF P hC hcirc) {r ρ : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (hρ : 0 < ρ) {z w : ℂ} (hw : ‖w - z‖ + ρ ≤ r) :
    cov[fun ω => hcirc ω r z - hcirc ω 1 z, fun ω => hcirc ω ρ w - hcirc ω r z; P] = 0 := by
  have hP := hh.isProbabilityMeasure
  have hR : 0 < ‖z‖ + 1 := by positivity
  have hwR : ‖w‖ + ρ ≤ ‖z‖ + 1 := by linarith [norm_sub_norm_le w z]
  have h1 := hh.covariance_incr_recentred_le hr hr1 hρ (z := z) (w := w) (R := ‖z‖ + 1) le_rfl hwR
  have h2 := hh.covariance_incr_recentred_le hr hr1 hr (z := z) (w := z) (R := ‖z‖ + 1) le_rfl
    (by linarith)
  have e : (fun ω => hcirc ω ρ w - hcirc ω r z) =
      fun ω => (hcirc ω ρ w - hcirc ω (‖z‖ + 1) 0) - (hcirc ω r z - hcirc ω (‖z‖ + 1) 0) := by
    funext ω
    ring
  rw [e, covariance_fun_sub_right (hh.memLp_two_circle_sub hr one_pos z z)
    (hh.memLp_two_circle_sub hρ hR w 0) (hh.memLp_two_circle_sub hr hR z 0), h1, h2,
    circlePairPotential_nested one_pos hr1 hρ.le hw, circlePairPotential_nested hr le_rfl hρ.le hw,
    circlePairPotential_self_center zero_le_one r, circlePairPotential_self_center hr.le r,
    max_eq_right hr1, max_self, Real.log_one]
  ring

/-- **Independence of the coarse increment from the fine field.** For `0 < r ≤ 1`, the increment
`h_r(z) - h_1(z)` is independent of the family `h'_ε(w) = h_{rε}(rw + z) - h_r(z)`, indexed by the pairs
`(ε, w)` with `ε > 0` and `‖w‖ + ε ≤ 1`. -/
theorem indepFun_incr_fine (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : ℂ) :
    IndepFun (fun ω => hcirc ω r z - hcirc ω 1 z)
      (fun ω (p : {p : ℝ × ℂ // 0 < p.1 ∧ ‖p.2‖ + p.1 ≤ 1}) =>
        hcirc ω (r * p.1.1) ((r : ℂ) * p.1.2 + z) - hcirc ω r z) P :=
  GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero hh.isGaussianProcess
    (hh.circle_sub_mem_span hr one_pos z z)
    (B := fun (p : {p : ℝ × ℂ // 0 < p.1 ∧ ‖p.2‖ + p.1 ≤ 1}) ω =>
      hcirc ω (r * p.1.1) ((r : ℂ) * p.1.2 + z) - hcirc ω r z)
    (fun p => hh.circle_sub_mem_span (mul_pos hr p.2.1) hr _ z)
    (fun p => hh.covariance_incr_fine_eq_zero hr hr1 (mul_pos hr p.2.1) (by
      have h1 : ‖(r : ℂ) * p.1.2 + z - z‖ = r * ‖p.1.2‖ := by
        rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      rw [h1]
      nlinarith [p.2.2]))

end IsWholePlaneGFF

end LatticeProb.Gauss
