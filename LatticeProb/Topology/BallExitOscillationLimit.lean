import LatticeProb.Topology.BallClockContinuity

/-! # Oscillation between neighboring ball exit times -/

set_option autoImplicit false

open Filter Set Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- Locally uniform convergence and coalescing interval endpoints imply vanishing
oscillation of the paths on those intervals. -/
theorem eventually_oscillation_lt_of_tendsto_endpoints
    {E α : Type*} [PseudoMetricSpace E] {l : Filter α}
    {F : α → C(ℝ≥0, E)} {f : C(ℝ≥0, E)} {a b : α → ℝ≥0} {τ : ℝ≥0}
    (hF : Tendsto F l (𝓝 f)) (ha : Tendsto a l (𝓝 τ)) (hb : Tendsto b l (𝓝 τ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
      dist (F i s) (F i t) < ε := by
  have heval : Continuous (fun p : C(ℝ≥0, E) × ℝ≥0 => p.1 p.2) :=
    ContinuousEval.continuous_eval
  have hnear : {p : C(ℝ≥0, E) × ℝ≥0 | dist (p.1 p.2) (f τ) < ε / 2} ∈ 𝓝 (f, τ) := by
    exact (heval.continuousAt.dist continuousAt_const) (Iio_mem_nhds (by simpa using half_pos hε))
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hnear
  have hinterval : ∀ᶠ i in l, Icc (a i) (b i) ⊆ V :=
    tendsto_smallSets_iff.mp (ha.Icc hb) V hV
  filter_upwards [hF.eventually hU, hinterval] with i hi hI s hs t ht
  have hs' : dist (F i s) (f τ) < ε / 2 := hUV (show (F i, s) ∈ U ×ˢ V from ⟨hi, hI hs⟩)
  have ht' : dist (F i t) (f τ) < ε / 2 := hUV (show (F i, t) ∈ U ×ˢ V from ⟨hi, hI ht⟩)
  have htri := dist_triangle (F i s) (f τ) (F i t)
  rw [dist_comm (f τ) (F i t)] at htri
  linarith

/-- Exit times in neighboring radii converge to the limiting finite exit time. -/
theorem tendsto_ballClock_toNNReal_of_radius
    {d : ℕ} {α : Type*} {l : Filter α} {F : α → Path d} {f : Path d}
    {R : α → ℝ} {r : ℝ} (hF : Tendsto F l (𝓝 f)) (hR : Tendsto R l (𝓝 r))
    (hunb : ¬ Bornology.IsBounded (Set.range f))
    (hc : ContinuousAt (fun s : ℝ => ballClock f s) r) :
    Tendsto (fun i => (ballClock (F i) (R i)).toNNReal) l
      (𝓝 (ballClock f r).toNNReal) := by
  have hfinite : ballClock f r ≠ ⊤ := ballClock_ne_top ⟨f, hunb⟩ r
  have hpair : Tendsto (fun i => (F i, R i)) l (𝓝 (f, r)) := hF.prodMk_nhds hR
  have hclock : Tendsto (fun i => ballClock (F i) (R i)) l (𝓝 (ballClock f r)) :=
    @tendsto_ballClock_of_continuousAt_radius d α l (fun i => (F i, R i)) (f, r)
      hpair hunb hc
  exact (ENNReal.tendsto_toNNReal hfinite).comp hclock

/-- At a radius-continuity point of an unbounded limiting path, oscillation
between neighboring ball exit times tends to zero under local uniform convergence. -/
theorem eventually_ballClock_neighbor_oscillation_lt
    {d : ℕ} {α : Type*} {l : Filter α} {F : α → Path d} {f : Path d}
    {δ : α → ℝ} {r : ℝ} (hF : Tendsto F l (𝓝 f))
    (hδ : Tendsto δ l (𝓝 0))
    (hunb : ¬ Bornology.IsBounded (Set.range f))
    (hc : ContinuousAt (fun s : ℝ => ballClock f s) r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ s ∈ Icc (ballClock (F i) (r - δ i)).toNNReal
        (ballClock (F i) (r + δ i)).toNNReal,
      ∀ t ∈ Icc (ballClock (F i) (r - δ i)).toNNReal
        (ballClock (F i) (r + δ i)).toNNReal,
      dist (F i s) (F i t) < ε := by
  have hminus : Tendsto (fun i => r - δ i) l (𝓝 r) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hδ)
  have hplus : Tendsto (fun i => r + δ i) l (𝓝 r) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hδ)
  have ha := tendsto_ballClock_toNNReal_of_radius hF hminus hunb hc
  have hb := tendsto_ballClock_toNNReal_of_radius hF hplus hunb hc
  exact eventually_oscillation_lt_of_tendsto_endpoints hF ha hb hε

end LatticeProb.UnboundedRayIntervalIntegrand
