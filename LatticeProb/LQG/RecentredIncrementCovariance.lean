import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.CircleCov

/-! # Covariances of circle-average increments -/

open MeasureTheory ProbabilityTheory
open LQGMetric.CircleAvg MatedCRTHarmonic.GMCFacts

namespace LatticeProb.LQG

/-- The covariance of a circle increment with a recentred average. -/
theorem covariance_increment_recentred {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    {a b s ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hε : 0 < ε)
    (t u z : ℂ) :
    cov[fun ω => H a t ω - H b t ω, fun ω => H s u ω - H ε z ω; P] =
      -circCov t a u s + circCov t b u s + circCov t a z ε - circCov t b z ε := by
  have := hH.isProbabilityMeasure
  have e : (fun ω => H a t ω - H b t ω) =
      (fun ω => (H a t ω - H ε z ω) - (H b t ω - H ε z ω)) := by
    funext ω
    ring
  have hA : MemLp (fun ω => H a t ω - H ε z ω) 2 P :=
    (memLp_two_coord hH ha t).sub (memLp_two_coord hH hε z)
  have hB : MemLp (fun ω => H b t ω - H ε z ω) 2 P :=
    (memLp_two_coord hH hb t).sub (memLp_two_coord hH hε z)
  have hC : MemLp (fun ω => H s u ω - H ε z ω) 2 P :=
    (memLp_two_coord hH hs u).sub (memLp_two_coord hH hε z)
  rw [e, covariance_fun_sub_left hA hB hC,
    cov_recentred hH hε ha hs z t u, cov_recentred hH hε hb hs z t u]
  ring

end LatticeProb.LQG
