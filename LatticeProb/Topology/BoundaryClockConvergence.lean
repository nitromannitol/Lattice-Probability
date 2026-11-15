import LatticeProb.Topology.BallExitOscillationLimit

/-! # Stability of boundary and exit clocks -/

set_option autoImplicit false

open Filter Set Metric
open scoped Topology NNReal

namespace LatticeProb

/-- A clock whose path position approaches a closed set cannot occur before a
compact initial path segment disjoint from that set. -/
theorem eventually_lt_clock_of_avoids_closed
    {E α : Type*} [MetricSpace E] {l : Filter α}
    {F : α → C(ℝ≥0, E)} {f : C(ℝ≥0, E)} {a : α → ℝ≥0}
    {K : Set E} (hK : IsClosed K) (hne : K.Nonempty)
    (hF : Tendsto F l (𝓝 f))
    (ha : Tendsto (fun i => infDist (F i (a i)) K) l (𝓝 0))
    {t : ℝ≥0} (havoid : ∀ s ≤ t, f s ∉ K) :
    ∀ᶠ i in l, t < a i := by
  have hcont : Continuous (fun s : ℝ≥0 => infDist (f s) K) :=
    (continuous_infDist_pt K).comp f.continuous
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ≥0) t).Nonempty from ⟨0, ⟨le_rfl, zero_le⟩⟩)
    hcont.continuousOn
  have hp : 0 < infDist (f s₀) K := (hK.notMem_iff_infDist_pos hne).1
    (havoid s₀ hs₀.2)
  let c := infDist (f s₀) K / 2
  have hc : 0 < c := half_pos hp
  have hopen : IsOpen {x : E | c < infDist x K} :=
    isOpen_lt continuous_const (continuous_infDist_pt K)
  have hmaps : MapsTo f (Icc 0 t) {x : E | c < infDist x K} := by
    intro s hs
    change c < infDist (f s) K
    exact lt_of_lt_of_le (half_lt_self hp) (hmin hs)
  have hpath := hF.eventually (ContinuousMap.eventually_mapsTo isCompact_Icc hopen hmaps)
  have hsmall : ∀ᶠ i in l, infDist (F i (a i)) K < c :=
    ha.eventually (Iio_mem_nhds hc)
  filter_upwards [hpath, hsmall] with i hi hs
  by_contra h
  have hle : a i ≤ t := le_of_not_gt h
  have := hi ⟨zero_le, hle⟩
  exact (not_lt_of_ge (le_of_lt this)) hs

end LatticeProb
