import Mathlib
import LatticeProb.LQG.LQGNegSplit

/-!
# Covariances of circle averages on two rescaled sub-squares

For the whole-plane Gaussian free field and the two sub-squares `z_s + R·T`, `T = [-1/8, 1/8]²`,
`z_s = ∓1/16`, we record the covariance identities behind the comparison of the field on the
sub-squares with `h_R(z_s)` plus an independent copy of the field.

* `LatticeProb.Gauss.circlePairPotential_affine`: scaling of the averaged logarithmic potential,
  `U(z + R c, R r, z + R w, R s) = log R + U(c, r, w, s)`.
* `LatticeProb.Gauss.IsWholePlaneGFF.covariance_circle_rescaled`: within one piece,
  `Cov(h_{Rδ}(z + R w), h_{Rδ}(z + R w')) = -log R + Cov(h_δ(w), h_δ(w'))`.
* `LatticeProb.Gauss.IsWholePlaneGFF.covariance_circle_across_pieces`: between the two pieces,
  `Cov(h_ε(x), h_ε(y)) ≤ 1 + Cov(h_R(z_s), h_R(z_{s'}))`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set

namespace LatticeProb.Gauss

open LatticeProb.LQG LQGDyadicScaling

/-- Scaling of the averaged logarithmic potential of a pair of circles:
`U(z + R c, R r, z + R w, R s) = log R + U(c, r, w, s)` for `R, s > 0`. -/
theorem circlePairPotential_affine {R : ℝ} (hR : 0 < R) (z c : ℂ) (r : ℝ) (w : ℂ) {s : ℝ}
    (hs : 0 < s) :
    circlePairPotential ((R : ℂ) * c + z) (R * r) ((R : ℂ) * w + z) (R * s) =
      Real.log R + circlePairPotential c r w s := by
  have hmap : ∀ θ : ℝ, circleMap ((R : ℂ) * c + z) (R * r) θ = (R : ℂ) * circleMap c r θ + z := by
    intro θ
    simp only [circleMap]
    push_cast
    ring
  have h1 : circlePairPotential ((R : ℂ) * c + z) (R * r) ((R : ℂ) * w + z) (R * s) =
      Real.circleAverage (fun x => Real.log R + Real.log (max s ‖x - w‖)) c r := by
    unfold circlePairPotential
    rw [Real.circleAverage_def, Real.circleAverage_def]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hmap]
    have h2 : (R : ℂ) * circleMap c r θ + z - ((R : ℂ) * w + z) = (R : ℂ) * (circleMap c r θ - w) := by
      ring
    have h3 : ‖(R : ℂ) * (circleMap c r θ - w)‖ = R * ‖circleMap c r θ - w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    rw [h2, h3, ← mul_max_of_nonneg _ _ hR.le,
      Real.log_mul hR.ne' (lt_of_lt_of_le hs (le_max_left _ _)).ne']
  rw [h1, circlePairPotential, Real.circleAverage_fun_add
    (continuous_const.continuousOn.circleIntegrable')
    ((continuous_log_max_norm_sub hs w).continuousOn.circleIntegrable'), Real.circleAverage_const]

theorem norm_rescaled_add_le {R δ : ℝ} (hR : 0 < R) {z w : ℂ} (hz : ‖z‖ + R ≤ 1)
    (hw : ‖w‖ + δ ≤ 1) : ‖(R : ℂ) * w + z‖ + R * δ ≤ 1 := by
  have h1 : ‖(R : ℂ) * w + z‖ ≤ R * ‖w‖ + ‖z‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Scaling of circle-average covariances inside a disc.** If `‖z‖ + R ≤ 1` and
`‖w‖ + δ, ‖w'‖ + δ ≤ 1`, then
`Cov(h_{Rδ}(R w + z), h_{Rδ}(R w' + z)) = -log R + Cov(h_δ(w), h_δ(w'))`. -/
theorem IsWholePlaneGFF.covariance_circle_rescaled (hh : IsWholePlaneGFF P hC hcirc) {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) {z : ℂ} (hz : ‖z‖ + R ≤ 1) {w w' : ℂ} (hw : ‖w‖ + δ ≤ 1)
    (hw' : ‖w'‖ + δ ≤ 1) :
    cov[fun ω => hcirc ω (R * δ) ((R : ℂ) * w + z), fun ω => hcirc ω (R * δ) ((R : ℂ) * w' + z); P] =
      -Real.log R + cov[fun ω => hcirc ω δ w, fun ω => hcirc ω δ w'; P] := by
  rw [hh.covariance_circle_inside (mul_pos hR hδ) (mul_pos hR hδ)
      (norm_rescaled_add_le hR hz hw) (norm_rescaled_add_le hR hz hw'),
    hh.covariance_circle_inside hδ hδ hw hw', circlePairPotential_affine hR z w δ w' hδ]
  ring

theorem norm_lqgSquareCentre_sub_of_ne {s s' : Fin 2} (h : s ≠ s') :
    ‖lqgSquareCentre s - lqgSquareCentre s'‖ = 1 / 8 := by
  fin_cases s <;> fin_cases s'
  · exact absurd rfl h
  · have := dist_lqgSquareCentre
    rwa [dist_eq_norm] at this
  · have := dist_lqgSquareCentre
    rwa [dist_comm, dist_eq_norm] at this
  · exact absurd rfl h

/-- **Circle averages on the two sub-squares are almost independent.** For `k ≥ 4`, `R = 2^{-k}`,
`w, w' ∈ [-1/8, 1/8]²` and `s ≠ s'`, the covariance of `h_ε(R w + z_s)` and `h_ε(R w' + z_{s'})`
is at most `1 + Cov(h_R(z_s), h_R(z_{s'}))`. -/
theorem IsWholePlaneGFF.covariance_circle_across_pieces (hh : IsWholePlaneGFF P hC hcirc) {k : ℕ}
    (hk : 4 ≤ k) {ε : ℝ} (hε : 0 < ε) {s s' : Fin 2} (hss : s ≠ s') {w w' : ℂ}
    (hw : w ∈ lqgSquare) (hw' : w' ∈ lqgSquare)
    (hx : ‖(dyadicScale k : ℂ) * w + lqgSquareCentre s‖ + ε ≤ 1)
    (hy : ‖(dyadicScale k : ℂ) * w' + lqgSquareCentre s'‖ + ε ≤ 1) :
    cov[fun ω => hcirc ω ε ((dyadicScale k : ℂ) * w + lqgSquareCentre s),
        fun ω => hcirc ω ε ((dyadicScale k : ℂ) * w' + lqgSquareCentre s'); P] ≤
      1 + cov[fun ω => hcirc ω (dyadicScale k) (lqgSquareCentre s),
        fun ω => hcirc ω (dyadicScale k) (lqgSquareCentre s'); P] := by
  have hR := dyadicScale_pos' k
  have hR16 := dyadicScale_le_sixteenth hk
  have hcen : ‖lqgSquareCentre s - lqgSquareCentre s'‖ = 1 / 8 := norm_lqgSquareCentre_sub_of_ne hss
  have hzs : ‖lqgSquareCentre s‖ + dyadicScale k ≤ 1 := by
    rw [norm_lqgSquareCentre]; linarith
  have hzs' : ‖lqgSquareCentre s'‖ + dyadicScale k ≤ 1 := by
    rw [norm_lqgSquareCentre]; linarith
  rw [hh.covariance_circle_of_two_mul_le hR hzs hzs' (by rw [hcen]; linarith), hcen]
  have hw4 : ‖w‖ ≤ 1 / 4 := by simpa using lqgSquare_subset_closedBall hw
  have hw4' : ‖w'‖ ≤ 1 / 4 := by simpa using lqgSquare_subset_closedBall hw'
  set d := ‖(dyadicScale k : ℂ) * w + lqgSquareCentre s -
    ((dyadicScale k : ℂ) * w' + lqgSquareCentre s')‖ with hd
  have hdge : 3 / 32 ≤ d := by
    have e1 : (dyadicScale k : ℂ) * w + lqgSquareCentre s -
        ((dyadicScale k : ℂ) * w' + lqgSquareCentre s') =
        (lqgSquareCentre s - lqgSquareCentre s') + (dyadicScale k : ℂ) * (w - w') := by ring
    have e2 : ‖(dyadicScale k : ℂ) * (w - w')‖ ≤ dyadicScale k * (1 / 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
      have := norm_sub_le w w'
      exact mul_le_mul_of_nonneg_left (by linarith) hR.le
    have e3 := norm_sub_norm_le (lqgSquareCentre s - lqgSquareCentre s')
      (-((dyadicScale k : ℂ) * (w - w')))
    rw [norm_neg, sub_neg_eq_add, ← e1, hcen] at e3
    nlinarith
  have hdpos : 0 < d := by linarith
  have hne : (dyadicScale k : ℂ) * w + lqgSquareCentre s ≠
      (dyadicScale k : ℂ) * w' + lqgSquareCentre s' := fun h => by
    rw [hd, h, sub_self, norm_zero] at hdge; linarith
  refine (hh.covariance_circle_le_log_two hε hx hy hne).trans ?_
  have hlog : Real.log 2 - Real.log d ≤ 1 + (-Real.log (1 / 8)) := by
    have h8 : 1 + (-Real.log (1 / 8)) = Real.log (Real.exp 1 * 8) := by
      rw [one_div, Real.log_inv, neg_neg, Real.log_mul (Real.exp_pos 1).ne' (by norm_num),
        Real.log_exp]
    rw [h8, ← Real.log_div two_ne_zero hdpos.ne']
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hdpos]
    have := Real.exp_one_gt_d9
    nlinarith
  exact hlog
end LatticeProb.Gauss
