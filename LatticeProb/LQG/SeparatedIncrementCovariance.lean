import LatticeProb.LQG.RecentredIncrementZero

/-! # Covariance of separated circle-average increments -/

open MeasureTheory ProbabilityTheory
open MatedCRTHarmonic.GMCFacts

namespace LatticeProb.LQG

/-- Circle-average increments over separated disks have zero covariance. -/
theorem covariance_increments_of_separated {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {t u : ℂ} (hfar : max c d + max a b ≤ ‖t - u‖) :
    cov[fun ω => H a t ω - H b t ω, fun ω => H c u ω - H d u ω; P] = 0 := by
  have := hH.isProbabilityMeasure
  have hR : 0 < max a b := ha.trans_le (le_max_left _ _)
  have hin : ‖t - t‖ + max a b ≤ max a b := by
    simpa only [sub_self, norm_zero, zero_add] using (le_rfl : max a b ≤ max a b)
  have h1 := covariance_increment_recentred_of_separated hH ha hb hc hR hin
    (show c + max a b ≤ ‖t - u‖ by linarith [le_max_left c d])
  have h2 := covariance_increment_recentred_of_separated hH ha hb hd hR hin
    (show d + max a b ≤ ‖t - u‖ by linarith [le_max_right c d])
  have hA : MemLp (fun ω => H a t ω - H b t ω) 2 P :=
    (memLp_two_coord hH ha t).sub (memLp_two_coord hH hb t)
  have hC : MemLp (fun ω => H c u ω - H (max a b) t ω) 2 P :=
    (memLp_two_coord hH hc u).sub (memLp_two_coord hH hR t)
  have hD : MemLp (fun ω => H d u ω - H (max a b) t ω) 2 P :=
    (memLp_two_coord hH hd u).sub (memLp_two_coord hH hR t)
  have heq : (fun ω => H c u ω - H d u ω) =
      (fun ω => (H c u ω - H (max a b) t ω) - (H d u ω - H (max a b) t ω)) := by
    funext ω
    ring
  rw [heq, covariance_fun_sub_right hA hC hD, h1, h2, sub_self]

end LatticeProb.LQG
