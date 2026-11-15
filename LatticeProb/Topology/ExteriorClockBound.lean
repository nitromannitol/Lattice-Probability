import LatticeProb.Topology.BallExitOscillationLimit

/-! # Exterior clock bounds under path convergence -/

set_option autoImplicit false

open Filter Set Metric
open scoped Topology NNReal

namespace LatticeProb

/-- If paths stay close to a closed set before their clocks, a limiting path
outside the set forces the clocks to occur by that time. -/
theorem eventually_clock_le_of_outside_closed
    {E α : Type*} [MetricSpace E] {l : Filter α}
    {F : α → C(ℝ≥0, E)} {f : C(ℝ≥0, E)} {b : α → ℝ≥0}
    {δ : α → ℝ} {K : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hF : Tendsto F l (𝓝 f)) (hδ : Tendsto δ l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ s < b i, infDist (F i s) K ≤ δ i)
    {s : ℝ≥0} (hs : f s ∉ K) : ∀ᶠ i in l, b i ≤ s := by
  have hp : 0 < infDist (f s) K := (hK.notMem_iff_infDist_pos hne).1 hs
  have hdist : Tendsto (fun i => infDist (F i s) K) l (𝓝 (infDist (f s) K)) :=
    ((continuous_infDist_pt K).tendsto (f s)).comp
      (((continuous_eval_const s).tendsto f).comp hF)
  have hlower : ∀ᶠ i in l, infDist (f s) K / 2 < infDist (F i s) K :=
    hdist.eventually (Ioi_mem_nhds (half_lt_self hp))
  have hsmall : ∀ᶠ i in l, δ i < infDist (f s) K / 2 :=
    hδ.eventually (Iio_mem_nhds (half_pos hp))
  filter_upwards [hbound, hlower, hsmall] with i hi hl hu
  by_contra hn
  exact (not_lt_of_ge (hi s (lt_of_not_ge hn))) (lt_trans hu hl)

end LatticeProb
