import LatticeProb.Topology.UnboundedRayIntervalIntegrand
import LatticeProb.Prob.BallExitRadius
import LatticeProb.Topology.BallExitIntervalConvergence

/-! # Almost-everywhere regularity of ball exit radii -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- For almost every radius the ball exit clock is continuous, and the radius is
    different from the initial distance to the origin. -/
theorem ae_ballClock_continuousAt_and_ne_initial {d : ℕ} (f : Path d) :
    ∀ᵐ r : ℝ ∂volume, ContinuousAt (fun s : ℝ => ballClock f s) r ∧
      r ≠ dist (f 0) 0 := by
  have hc : ∀ᵐ r : ℝ ∂volume, ContinuousAt (fun s : ℝ => ballClock f s) r :=
    ae_continuousAt_openExitTime_ball_radius (fun t (g : Path d) => g t) f 0
  have hn : ∀ᵐ r : ℝ ∂volume, r ≠ dist (f 0) 0 := Measure.ae_ne volume _
  exact hc.and hn

/-- Interval-distance convergence at a regular radius for convergent unbounded rays. -/
theorem tendsto_intervalEDist_unboundedRay {d : ℕ} {α : Type*} {l : Filter α}
    {F : α → UnboundedRay d} {f : UnboundedRay d} (hF : Tendsto F l (𝓝 f))
    {r : ℝ} (hc : ContinuousAt (fun s : ℝ => ballClock f.1 s) r)
    (hne : r ≠ dist (f.1 0) 0) :
    Tendsto (fun i => IntervalReparamEDist.intervalEDist (F i).1 f.1
      (ballClock (F i).1 r) (ballClock f.1 r)) l (𝓝 0) := by
  have hp : Tendsto (fun i => (F i).1) l (𝓝 f.1) :=
    (continuous_subtype_val.tendsto f).comp hF
  have hpair : Tendsto (fun i => ((F i).1, r)) l (𝓝 (f.1, r)) :=
    hp.prodMk_nhds tendsto_const_nhds
  have hfinite : ∀ᶠ i in l, ballClock (F i).1 r ≠ ⊤ :=
    Eventually.of_forall (fun i => ballClock_ne_top (F i) r)
  exact @tendsto_intervalEDist_ballClock d α l (fun i => ((F i).1, r)) (f.1, r)
    hpair f.2 hc hfinite hne

/-- Exit-interval distances converge at almost every radius along convergent rays. -/
theorem ae_tendsto_intervalEDist {d : ℕ} {α : Type*} {l : Filter α}
    {F : α → UnboundedRay d} {f : UnboundedRay d} (hF : Tendsto F l (𝓝 f)) :
    ∀ᵐ r : ℝ ∂volume.restrict (Set.Ioi (1 : ℝ)),
      Tendsto (fun i => IntervalReparamEDist.intervalEDist (F i).1 f.1
        (ballClock (F i).1 r) (ballClock f.1 r)) l (𝓝 0) := by
  have ha : ∀ᵐ r : ℝ ∂volume.restrict (Set.Ioi (1 : ℝ)),
      ContinuousAt (fun s : ℝ => ballClock f.1 s) r ∧ r ≠ dist (f.1 0) 0 :=
    ae_restrict_of_ae (ae_ballClock_continuousAt_and_ne_initial f.1)
  filter_upwards [ha] with r hr
  exact tendsto_intervalEDist_unboundedRay hF hr.1 hr.2

end LatticeProb.UnboundedRayIntervalIntegrand
