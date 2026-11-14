import LatticeProb.Topology.BallClockLowerSemicontinuity
import LatticeProb.Topology.BallClockNeighborUpper

/-! # Joint continuity of ball exit times -/

set_option autoImplicit false

open Filter Set
open scoped ENNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

variable {d : ℕ}

/-- Joint path-radius convergence implies convergence of exit times whenever the limiting
path has unbounded range and its exit time is continuous in the radius. -/
theorem tendsto_ballClock_of_continuousAt_radius {α : Type*} {l : Filter α}
    {F : α → Path d × ℝ} {p : Path d × ℝ} (hF : Tendsto F l (𝓝 p))
    (hunb : ¬ Bornology.IsBounded (Set.range p.1))
    (hc : ContinuousAt (fun r : ℝ => ballClock p.1 r) p.2) :
    Tendsto (fun i => ballClock (F i).1 (F i).2) l (𝓝 (ballClock p.1 p.2)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact eventually_lt_ballClock hF ha
  · intro b hb
    have hs : ∀ᶠ s in 𝓝[>] p.2, ballClock p.1 s < b :=
      nhdsWithin_le_nhds (hc (Iio_mem_nhds hb))
    have hs' : ∀ᶠ s in 𝓝[>] p.2, p.2 < s ∧ ballClock p.1 s < b := by
      filter_upwards [self_mem_nhdsWithin, hs] with s hrs hsb
      exact ⟨hrs, hsb⟩
    obtain ⟨s, hrs, hsb⟩ := hs'.exists
    have hfin : ballClock p.1 s ≠ ⊤ := ballClock_ne_top ⟨p.1, hunb⟩ s
    filter_upwards [eventually_ballClock_le_larger hF hrs hfin] with i hi
    exact lt_of_le_of_lt hi hsb

/-- The joint ball exit time is continuous at such a path and radius. -/
theorem continuousAt_ballClock_of_continuousAt_radius (p : Path d × ℝ)
    (hunb : ¬ Bornology.IsBounded (Set.range p.1))
    (hc : ContinuousAt (fun r : ℝ => ballClock p.1 r) p.2) :
    ContinuousAt (fun q : Path d × ℝ => ballClock q.1 q.2) p :=
  tendsto_ballClock_of_continuousAt_radius tendsto_id hunb hc

end LatticeProb.UnboundedRayIntervalIntegrand
