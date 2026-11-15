import LatticeProb.Topology.BoundaryClockConvergence
import LatticeProb.Topology.ExteriorClockBound

/-! # Convergence of ordered clocks -/

set_option autoImplicit false

open Filter Set Metric
open scoped Topology NNReal

namespace LatticeProb

/-- Two ordered clocks converge to a regular limiting exit time when the first
approaches a closed boundary and the path stays near a closed domain until the second. -/
theorem tendsto_ordered_clocks_of_regular_exit
    {E α : Type*} [MetricSpace E] {l : Filter α}
    {F : α → C(ℝ≥0, E)} {f : C(ℝ≥0, E)} {a b : α → ℝ≥0}
    {δ : α → ℝ} {K C : Set E} {τ : ℝ≥0}
    (hK : IsClosed K) (hKne : K.Nonempty) (hC : IsClosed C) (hCne : C.Nonempty)
    (hF : Tendsto F l (𝓝 f))
    (ha : Tendsto (fun i => infDist (F i (a i)) K) l (𝓝 0))
    (hδ : Tendsto δ l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ s < b i, infDist (F i s) C ≤ δ i)
    (horder : ∀ᶠ i in l, a i ≤ b i)
    (hbefore : ∀ s < τ, f s ∉ K)
    (hafter : ∀ t > τ, ∃ s < t, f s ∉ C) :
    Tendsto a l (𝓝 τ) ∧ Tendsto b l (𝓝 τ) := by
  have hlower : ∀ t < τ, ∀ᶠ i in l, t < a i := by
    intro t ht
    exact eventually_lt_clock_of_avoids_closed hK hKne hF ha
      (fun s hs => hbefore s (lt_of_le_of_lt hs ht))
  have hupper : ∀ t > τ, ∀ᶠ i in l, b i < t := by
    intro t ht
    obtain ⟨s, hst, hs⟩ := hafter t ht
    filter_upwards [eventually_clock_le_of_outside_closed hC hCne hF hδ hbound hs] with i hi
    exact lt_of_le_of_lt hi hst
  constructor
  · apply tendsto_order.2
    constructor
    · exact hlower
    · intro t ht
      filter_upwards [horder, hupper t ht] with i hi hu
      exact lt_of_le_of_lt hi hu
  · apply tendsto_order.2
    constructor
    · intro t ht
      filter_upwards [hlower t ht, horder] with i hl hi
      exact lt_of_lt_of_le hl hi
    · exact hupper

/-- The oscillation between two such clocks vanishes. -/
theorem eventually_ordered_clock_oscillation_lt
    {E α : Type*} [MetricSpace E] {l : Filter α}
    {F : α → C(ℝ≥0, E)} {f : C(ℝ≥0, E)} {a b : α → ℝ≥0}
    {δ : α → ℝ} {K C : Set E} {τ : ℝ≥0}
    (hK : IsClosed K) (hKne : K.Nonempty) (hC : IsClosed C) (hCne : C.Nonempty)
    (hF : Tendsto F l (𝓝 f))
    (ha : Tendsto (fun i => infDist (F i (a i)) K) l (𝓝 0))
    (hδ : Tendsto δ l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ s < b i, infDist (F i s) C ≤ δ i)
    (horder : ∀ᶠ i in l, a i ≤ b i)
    (hbefore : ∀ s < τ, f s ∉ K)
    (hafter : ∀ t > τ, ∃ s < t, f s ∉ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ s ∈ Icc (a i) (b i), ∀ t ∈ Icc (a i) (b i),
      dist (F i s) (F i t) < ε := by
  obtain ⟨ha', hb'⟩ := tendsto_ordered_clocks_of_regular_exit
    hK hKne hC hCne hF ha hδ hbound horder hbefore hafter
  exact UnboundedRayIntervalIntegrand.eventually_oscillation_lt_of_tendsto_endpoints hF ha' hb' hε

end LatticeProb
