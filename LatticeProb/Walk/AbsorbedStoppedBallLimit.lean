import LatticeProb.Walk.AbsorbedStoppedBallComparison
import LatticeProb.Topology.BallExitOscillationReparam

/-! # Limits of stopped terminal-absorbed paths -/

set_option autoImplicit false

open Filter Set Metric
open scoped NNReal ENNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- If absorbed paths are uniformly close and the reference endpoints lie beyond
 a buffered ball, then their paths stopped at the inner ball are uniformly close
 in the limit, provided the reference paths converge after time changes to an
 unbounded path with a radius-continuous exit clock. -/
theorem eventually_dist_stopped_ball_lt_of_absorbed_dist
    {d : ℕ} {α : Type*} {l : Filter α}
    (F G : α → Path d) (T U : α → ℝ≥0) (φ ψ : α → ℝ≥0 ≃o ℝ≥0)
    (e : α → ℝ) (R : ℝ) (g : Path d)
    (hG : Tendsto (fun i => (G i).comp ⟨ψ i, (ψ i).continuous⟩) l (𝓝 g))
    (he : Tendsto e l (𝓝 0))
    (hunb : ¬ Bornology.IsBounded (Set.range g))
    (hc : ContinuousAt (fun r : ℝ => ballClock g r) R)
    (hclose : ∀ᶠ i in l, ∀ t, dist (F i (min t (T i)))
      (G i (min (φ i t) (U i))) ≤ e i)
    (hmargin : ∀ᶠ i in l, R + 2 * e i ≤ dist (G i (U i)) 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ t : ℝ≥0,
      dist (F i (min t (ballClock (F i) R).toNNReal))
        (G i (min (φ i t) (ballClock (G i) R).toNNReal)) < ε := by
  have hosc := eventually_ballClock_neighbor_oscillation_lt_of_reparam ψ hG he hunb hc
    (half_pos hε)
  have hesmall : ∀ᶠ i in l, e i < ε / 2 := he (Iio_mem_nhds (half_pos hε))
  filter_upwards [hosc, hesmall, hclose, hmargin] with i hi he' hcl hm t
  have hb := dist_stopped_ball_le_of_absorbed_dist_le (F i) (G i) (T i) (U i)
    (φ i) 0 R (e i) (ε / 2) (F i).continuous hcl hm
    (by
      intro s hs u hu
      exact le_of_lt (hi s hs u hu)) t
  change dist (F i (min t (ballClock (F i) R).toNNReal))
      (G i (min (φ i t) (ballClock (G i) R).toNNReal)) ≤ e i + ε / 2 at hb
  linarith

end LatticeProb.UnboundedRayIntervalIntegrand
