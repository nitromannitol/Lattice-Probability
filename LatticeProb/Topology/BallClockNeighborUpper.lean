import LatticeProb.Topology.UnboundedRayIntervalIntegrand

/-! # Stability of ball exit times across neighboring radii -/

set_option autoImplicit false

open Filter Set Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

variable {d : ℕ}

/-- Along convergent paths and radii, the exit time is eventually bounded by the limiting
path's finite exit time at any strictly larger radius. -/
theorem eventually_ballClock_le_larger {α : Type*} {l : Filter α}
    {F : α → Path d × ℝ} {p : Path d × ℝ} (hF : Tendsto F l (𝓝 p))
    {s : ℝ} (hrs : p.2 < s) (hs : ballClock p.1 s ≠ ⊤) :
    ∀ᶠ i in l, ballClock (F i).1 (F i).2 ≤ ballClock p.1 s := by
  let t : ℝ≥0 := (ballClock p.1 s).toNNReal
  have hout := openExitTime_not_mem (B := fun t (f : Path d) => f t)
    (ω := p.1) (isOpen_ball : IsOpen (ball (0 : EuclideanSpace ℝ (Fin d)) s))
    p.1.continuous hs
  have hdist : s ≤ dist (p.1 t) 0 := by
    simpa only [Metric.mem_ball, not_lt, ballClock, t] using hout
  have heval : Continuous (fun q : Path d × ℝ => q.1 t) :=
    (ContinuousEval.continuous_eval (F := Path d)).comp
      (continuous_fst.prodMk continuous_const)
  have hopen : IsOpen {q : Path d × ℝ | q.2 < dist (q.1 t) 0} :=
    isOpen_lt continuous_snd (heval.dist continuous_const)
  have hmem : p ∈ {q : Path d × ℝ | q.2 < dist (q.1 t) 0} := lt_of_lt_of_le hrs hdist
  filter_upwards [hF.eventually (hopen.mem_nhds hmem)] with i hi
  have hout' : (F i).1 t ∉ ball (0 : EuclideanSpace ℝ (Fin d)) (F i).2 := by
    simpa only [Metric.mem_ball, not_lt] using le_of_lt hi
  have hle := openExitTime_le_of_not_mem (B := fun t (f : Path d) => f t)
    (ω := (F i).1) hout'
  change ballClock (F i).1 (F i).2 ≤ ((ballClock p.1 s).toNNReal : ℝ≥0∞) at hle
  rw [ENNReal.coe_toNNReal hs] at hle
  exact hle

end LatticeProb.UnboundedRayIntervalIntegrand
