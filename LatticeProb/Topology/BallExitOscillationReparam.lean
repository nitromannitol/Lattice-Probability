import LatticeProb.Topology.BallExitOscillationLimit
import LatticeProb.Prob.OpenExitTimeReparam

/-! # Neighboring ball exits under changes of clock -/

set_option autoImplicit false

open Filter Set Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- If time-changed paths converge locally uniformly to an unbounded path whose
ball-exit clock is continuous at a radius, the oscillation of the original
paths between neighboring ball exits vanishes. -/
theorem eventually_ballClock_neighbor_oscillation_lt_of_reparam
    {d : ℕ} {α : Type*} {l : Filter α} {F : α → Path d} {f : Path d}
    (φ : α → ℝ≥0 ≃o ℝ≥0) {δ : α → ℝ} {r : ℝ}
    (hF : Tendsto (fun i => (F i).comp ⟨φ i, (φ i).continuous⟩) l (𝓝 f))
    (hδ : Tendsto δ l (𝓝 0))
    (hunb : ¬ Bornology.IsBounded (Set.range f))
    (hc : ContinuousAt (fun s : ℝ => ballClock f s) r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ s ∈ Icc (ballClock (F i) (r - δ i)).toNNReal
        (ballClock (F i) (r + δ i)).toNNReal,
      ∀ t ∈ Icc (ballClock (F i) (r - δ i)).toNNReal
        (ballClock (F i) (r + δ i)).toNNReal,
      dist (F i s) (F i t) < ε := by
  let G : α → Path d := fun i => (F i).comp ⟨φ i, (φ i).continuous⟩
  have hg : Tendsto G l (𝓝 f) := hF
  have hminus : Tendsto (fun i => r - δ i) l (𝓝 r) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hδ)
  have hplus : Tendsto (fun i => r + δ i) l (𝓝 r) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hδ)
  have hlim : ballClock f r < ⊤ := lt_top_iff_ne_top.mpr (ballClock_ne_top ⟨f, hunb⟩ r)
  have hm : ∀ᶠ i in l, ballClock (G i) (r - δ i) ≠ ⊤ := by
    have h := tendsto_ballClock_of_continuousAt_radius (hg.prodMk_nhds hminus) hunb hc
    filter_upwards [h (Iio_mem_nhds hlim)] with i hi
    exact ne_of_lt hi
  have hp : ∀ᶠ i in l, ballClock (G i) (r + δ i) ≠ ⊤ := by
    have h := tendsto_ballClock_of_continuousAt_radius (hg.prodMk_nhds hplus) hunb hc
    filter_upwards [h (Iio_mem_nhds hlim)] with i hi
    exact ne_of_lt hi
  have hosc := eventually_ballClock_neighbor_oscillation_lt hg hδ hunb hc (half_pos hε)
  filter_upwards [hm, hp, hosc] with i hm hp hi
  have hfin (R : ℝ) (h : ballClock (G i) R ≠ ⊤) : ballClock (F i) R ≠ ⊤ := by
    have hout := openExitTime_not_mem (B := fun t (_ : Unit) => G i t) (ω := ())
      (isOpen_ball : IsOpen (ball (0 : EuclideanSpace ℝ (Fin d)) R)) (G i).continuous h
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (openExitTime_le_of_not_mem
      (B := fun t (_ : Unit) => F i t) (ω := ()) hout)
  have hbound : ∀ s ∈ Icc (ballClock (F i) (r - δ i)).toNNReal
        (ballClock (F i) (r + δ i)).toNNReal,
      ∀ t ∈ Icc (ballClock (F i) (r - δ i)).toNNReal
        (ballClock (F i) (r + δ i)).toNNReal,
      dist (F i s) (F i t) ≤ ε / 2 := by
    apply (openExitTime_comp_orderIso_oscillation_iff (F i)
      (ball 0 (r - δ i)) (ball 0 (r + δ i)) (φ i) (ε / 2)
      isOpen_ball isOpen_ball (F i).continuous (hfin _ hm) (hfin _ hp)).mp
    intro s hs t ht
    exact le_of_lt (hi s hs t ht)
  intro s hs t ht
  exact lt_of_le_of_lt (hbound s hs t ht) (half_lt_self hε)

end LatticeProb.UnboundedRayIntervalIntegrand
