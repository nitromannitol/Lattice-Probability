import LatticeProb.Walk.AbsorbedStoppedBallLimit

/-! # Stopped path limits with a fixed endpoint buffer -/

set_option autoImplicit false

open Filter Set Metric
open scoped NNReal ENNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- A fixed positive buffer around the stopping ball supplies the endpoint
margin needed to pass from terminal-absorbed to stopped-path convergence. -/
theorem eventually_dist_stopped_ball_lt_of_fixed_buffer
    {d : ℕ} {α : Type*} {l : Filter α}
    (F G : α → Path d) (T U : α → ℝ≥0) (φ ψ : α → ℝ≥0 ≃o ℝ≥0)
    (e : α → ℝ) (R δ : ℝ) (g : Path d)
    (hG : Tendsto (fun i => (G i).comp ⟨ψ i, (ψ i).continuous⟩) l (𝓝 g))
    (he : Tendsto e l (𝓝 0))
    (hunb : ¬ Bornology.IsBounded (Set.range g))
    (hc : ContinuousAt (fun r : ℝ => ballClock g r) R)
    (hclose : ∀ᶠ i in l, ∀ t, dist (F i (min t (T i)))
      (G i (min (φ i t) (U i))) ≤ e i)
    (hδ : 0 < δ)
    (hbuffer : ∀ᶠ i in l, G i (U i) ∉ Metric.ball 0 (R + δ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ t : ℝ≥0,
      dist (F i (min t (ballClock (F i) R).toNNReal))
        (G i (min (φ i t) (ballClock (G i) R).toNNReal)) < ε := by
  apply eventually_dist_stopped_ball_lt_of_absorbed_dist F G T U φ ψ e R g
    hG he hunb hc hclose ?_ hε
  have hevent : ∀ᶠ i in l, e i < δ / 2 := he (Iio_mem_nhds (half_pos hδ))
  filter_upwards [hevent, hbuffer] with i hi hb
  simp only [Metric.mem_ball, not_lt] at hb
  linarith

end LatticeProb.UnboundedRayIntervalIntegrand
