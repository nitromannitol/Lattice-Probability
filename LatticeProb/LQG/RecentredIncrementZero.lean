import LatticeProb.LQG.RecentredIncrementCovariance
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6C

/-! # Vanishing covariances of circle-average increments -/

open MeasureTheory ProbabilityTheory Metric
open LQGMetric.CircleAvg MatedCRTHarmonic.GMCFacts
open MatedCRTHarmonic.MoTPort.ConeArea6

namespace LatticeProb.LQG

/-- A fine increment is uncorrelated with a coarser recentred average at the same center. -/
theorem covariance_increment_recentred_same_center {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    {a b s ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hε : 0 < ε)
    (has : a ≤ s) (hbs : b ≤ s) {t z : ℂ}
    (hinside : ‖t - z‖ + max a b ≤ ε) :
    cov[fun ω => H a t ω - H b t ω, fun ω => H s t ω - H ε z ω; P] = 0 := by
  rw [covariance_increment_recentred hH ha hb hs hε,
    circCov_same ha hs, circCov_same hb hs,
    max_eq_left has, max_eq_left hbs,
    circCov_of_inside ha hε (by linarith [le_max_left a b]),
    circCov_of_inside hb hε (by linarith [le_max_right a b])]
  ring

/-- A fine increment is uncorrelated with a sufficiently distant recentred average. -/
theorem covariance_increment_recentred_of_separated {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    {a b s ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hε : 0 < ε)
    {t u z : ℂ} (hinside : ‖t - z‖ + max a b ≤ ε)
    (hfar : s + max a b ≤ ‖t - u‖) :
    cov[fun ω => H a t ω - H b t ω, fun ω => H s u ω - H ε z ω; P] = 0 := by
  have hpot : ∀ r, 0 < r → r ≤ max a b →
      circCov t r u s = Real.log ‖t - u‖ := by
    intro r hr hrmax
    rw [circCov_eq_of_outside hr hs (fun x hx => ?_), max_eq_right (by linarith)]
    rw [mem_sphere_iff_norm, norm_sub_rev] at hx
    have ht := norm_sub_norm_le (t - u) (t - x)
    rw [show t - u - (t - x) = x - u by ring, norm_sub_rev x u] at ht
    linarith
  rw [covariance_increment_recentred hH ha hb hs hε,
    hpot a ha (le_max_left _ _), hpot b hb (le_max_right _ _),
    circCov_of_inside ha hε (by linarith [le_max_left a b]),
    circCov_of_inside hb hε (by linarith [le_max_right a b])]
  ring

end LatticeProb.LQG
