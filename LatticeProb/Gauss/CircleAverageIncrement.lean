import LatticeProb.Gauss.CircleAverageCovariance

/-!
# Increment variance of the circle average process of the whole-plane GFF

Let `h` be a whole-plane GFF with circle averages `h_r(z)`. The variance of an increment of the circle average
process `(r, z) ↦ h_r(z)` in the radius and in the centre satisfies
`Var[h_s(z) - h_{s'}(z')] ≤ 2 (|s - s'| + |z - z'|) / min(s, s')`
for all `s, s' > 0` and all `z, z' ∈ ℂ`. This is the input of the Kolmogorov-Chentsov argument for the modulus of
continuity of the circle average process at a fixed scale (Duplantier-Sheffield 2011, Proposition 3.1; Hu-Miller-Peres
2010).

The covariance of `h_s(z)` and `h_{s'}(z')` is `avg_{∂B_s(z)} log max(|·|,1) + avg_{∂B_{s'}(z')} log max(|·|,1) -
avg_{x ∈ ∂B_s(z)} log max(s', |x - z'|)` (`wholePlaneGFFCov_circle_circle_eq`). In the variance of the increment the
first two terms cancel, and what remains is, on each of the two circles, the average of the difference of the
logarithmic potentials `log max(s', |x - z'|) - log max(s, |x - z|)`, which is at most
`(|s - s'| + |z - z'|) / min(s, s')` at every point `x`.

## Main statements

* `LatticeProb.Gauss.abs_log_max_norm_sub_sub_le`: the pointwise bound of the two potentials;
* `LatticeProb.Gauss.circlePairPotential_sub_le`: the same bound for their averages over any circle;
* `LatticeProb.Gauss.IsWholePlaneGFF.variance_circle_sub_eq`: the exact increment variance;
* `LatticeProb.Gauss.IsWholePlaneGFF.variance_circle_sub_le`: the increment variance bound.
-/

open MeasureTheory ProbabilityTheory Metric

namespace LatticeProb.Gauss

/-- **Lipschitz bound of the logarithmic potentials.** For `s, s' > 0`, the potentials `log max(s, |x - z|)` and
`log max(s', |x - z'|)` differ by at most `(|s - s'| + |z - z'|) / min(s, s')` at every point `x`. -/
theorem abs_log_max_norm_sub_sub_le {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') (x z z' : ℂ) :
    |Real.log (max s' ‖x - z'‖) - Real.log (max s ‖x - z‖)| ≤ (|s - s'| + ‖z - z'‖) / min s s' := by
  set a := max s ‖x - z‖ with ha_def
  set b := max s' ‖x - z'‖ with hb_def
  have hm : 0 < min s s' := lt_min hs hs'
  have ha : min s s' ≤ a := (min_le_left _ _).trans (le_max_left _ _)
  have hb : min s s' ≤ b := (min_le_right _ _).trans (le_max_left _ _)
  have ha0 : 0 < a := hm.trans_le ha
  have hb0 : 0 < b := hm.trans_le hb
  have hab : |b - a| ≤ |s - s'| + ‖z - z'‖ := by
    have h1 := abs_max_sub_max_le_max s' ‖x - z'‖ s ‖x - z‖
    have h2 : |‖x - z'‖ - ‖x - z‖| ≤ ‖z - z'‖ := by
      have h := abs_norm_sub_norm_le (x - z') (x - z)
      rwa [show x - z' - (x - z) = z - z' by ring] at h
    rw [abs_sub_comm s' s] at h1
    exact h1.trans (max_le (le_add_of_nonneg_right (norm_nonneg _))
      (h2.trans (le_add_of_nonneg_left (abs_nonneg _))))
  have k1 : Real.log b - Real.log a ≤ |b - a| / min s s' := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    calc Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
      _ = (b - a) / a := by field_simp
      _ ≤ |b - a| / a := by gcongr; exact le_abs_self _
      _ ≤ |b - a| / min s s' := by gcongr
  have k2 : Real.log a - Real.log b ≤ |b - a| / min s s' := by
    rw [← Real.log_div ha0.ne' hb0.ne', abs_sub_comm]
    calc Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ |a - b| / b := by gcongr; exact le_abs_self _
      _ ≤ |a - b| / min s s' := by gcongr
  have k3 : |b - a| / min s s' ≤ (|s - s'| + ‖z - z'‖) / min s s' := by gcongr
  rw [abs_le]
  constructor <;> linarith

/-- **Averaged Lipschitz bound.** Over any circle `∂B_r(c)`, the averaged potentials of `∂B_s(z)` and `∂B_{s'}(z')`
differ by at most `(|s - s'| + |z - z'|) / min(s, s')`. -/
theorem circlePairPotential_sub_le {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') (c : ℂ) (r : ℝ) (z z' : ℂ) :
    circlePairPotential c r z' s' - circlePairPotential c r z s ≤ (|s - s'| + ‖z - z'‖) / min s s' := by
  unfold circlePairPotential
  rw [← Real.circleAverage_sub (continuous_log_max_norm_sub hs' z').continuousOn.circleIntegrable'
    (continuous_log_max_norm_sub hs z).continuousOn.circleIntegrable']
  refine Real.circleAverage_mono_on_of_le_circle
    ((continuous_log_max_norm_sub hs' z').sub (continuous_log_max_norm_sub hs z)).continuousOn.circleIntegrable'
    fun x _ => ?_
  rw [Pi.sub_apply]
  exact (le_abs_self _).trans (abs_log_max_norm_sub_sub_le hs hs' x z z')

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Exact increment variance.** For `s, s' > 0`, the variance of `h_s(z) - h_{s'}(z')` is the sum over the two
circles of the averaged difference of the logarithmic potentials of the other circle and of the circle itself. -/
theorem variance_circle_sub_eq (hh : IsWholePlaneGFF P hC hcirc) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (z z' : ℂ) :
    Var[fun ω => hcirc ω s z - hcirc ω s' z'; P] =
      (circlePairPotential z s z' s' - circlePairPotential z s z s) +
        (circlePairPotential z' s' z s - circlePairPotential z' s' z' s') := by
  have hP := hh.isProbabilityMeasure
  have m1 := hh.memLp_two_circle hs z
  have m2 := hh.memLp_two_circle hs' z'
  rw [show (fun ω => hcirc ω s z - hcirc ω s' z') = (fun ω => hcirc ω s z) - fun ω => hcirc ω s' z' from rfl,
    variance_sub m1 m2, ← covariance_self m1.aestronglyMeasurable.aemeasurable,
    ← covariance_self m2.aestronglyMeasurable.aemeasurable]
  have c11 := hh.covariance_circle_circle hs hs z z
  have c22 := hh.covariance_circle_circle hs' hs' z' z'
  have c12 := hh.covariance_circle_circle hs hs' z z'
  have c21 : cov[fun ω => hcirc ω s z, fun ω => hcirc ω s' z'; P] =
      wholePlaneGFFCov (.circle s' z') (.circle s z) := by
    rw [covariance_comm]
    exact hh.covariance_circle_circle hs' hs z' z
  rw [wholePlaneGFFCov_circle_circle_eq hs s z z] at c11
  rw [wholePlaneGFFCov_circle_circle_eq hs' s' z' z'] at c22
  rw [wholePlaneGFFCov_circle_circle_eq hs' s z z'] at c12
  rw [wholePlaneGFFCov_circle_circle_eq hs s' z' z] at c21
  rw [c11, c22]
  linarith

/-- **Increment variance bound** for the circle average process: for `s, s' > 0` and all centres `z, z'`,
`Var[h_s(z) - h_{s'}(z')] ≤ 2 (|s - s'| + |z - z'|) / min(s, s')`. -/
theorem variance_circle_sub_le (hh : IsWholePlaneGFF P hC hcirc) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (z z' : ℂ) :
    Var[fun ω => hcirc ω s z - hcirc ω s' z'; P] ≤ 2 * ((|s - s'| + ‖z - z'‖) / min s s') := by
  rw [hh.variance_circle_sub_eq hs hs' z z']
  have e1 := circlePairPotential_sub_le hs hs' z s z z'
  have e2 := circlePairPotential_sub_le hs' hs z' s' z' z
  rw [abs_sub_comm s' s, norm_sub_rev z' z, min_comm s' s] at e2
  linarith

end IsWholePlaneGFF

end LatticeProb.Gauss
