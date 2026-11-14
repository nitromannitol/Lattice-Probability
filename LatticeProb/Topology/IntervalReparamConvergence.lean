import LatticeProb.Topology.IntervalReparamScale

/-! # Convergence of finite interval reparametrization distances -/

set_option autoImplicit false

open Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb.IntervalReparamEDist

/-- Locally uniform convergence of paths and convergence of positive finite durations
imply convergence of the interval distance to zero. -/
theorem tendsto_intervalEDist_of_positive_duration {d : ℕ} {α : Type*} {l : Filter α}
    {F : α → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0}
    {p : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) × ℝ≥0}
    (hF : Tendsto F l (𝓝 p)) (hp : 0 < p.2) :
    Tendsto (fun i => intervalEDist (F i).1 p.1 (F i).2 p.2) l (𝓝 0) := by
  have hpos : ∀ᶠ i in l, 0 < (F i).2 :=
    hF ((continuous_snd.tendsto p) (isOpen_Ioi.mem_nhds hp))
  have hc : Tendsto (fun i => normalizedPrefixCurve (F i).1 (F i).2) l
      (𝓝 (normalizedPrefixCurve p.1 p.2)) :=
    (continuous_normalizedPrefixCurve.tendsto p).comp hF
  have hd : Tendsto (fun i => edist (normalizedPrefixCurve (F i).1 (F i).2)
      (normalizedPrefixCurve p.1 p.2)) l (𝓝 0) := by
    simpa only [edist_self] using hc.edist (tendsto_const_nhds : Tendsto (fun _ : α =>
      normalizedPrefixCurve p.1 p.2) l (𝓝 (normalizedPrefixCurve p.1 p.2)))
  apply hd.congr'
  filter_upwards [hpos] with i hi
  exact (intervalEDist_eq_edist_normalizedPrefixCurve (F i).1 p.1 (F i).2 p.2 hi hp).symm

end LatticeProb.IntervalReparamEDist
