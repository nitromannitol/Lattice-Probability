import LatticeProb.Topology.BallClockContinuity
import LatticeProb.Topology.IntervalReparamConvergence
import LatticeProb.Topology.IntervalReparamZero

/-! # Convergence of interval distances at ball exit times -/

set_option autoImplicit false

open Filter Set Metric
open scoped ENNReal NNReal Topology

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- At a radius-continuity point away from the initial distance, ball-exit interval
    distances tend to zero under joint path-radius convergence. -/
theorem tendsto_intervalEDist_ballClock {d : ℕ} {α : Type*} {l : Filter α}
    {F : α → Path d × ℝ} {p : Path d × ℝ} (hF : Tendsto F l (𝓝 p))
    (hunb : ¬ Bornology.IsBounded (Set.range p.1))
    (hc : ContinuousAt (fun r : ℝ => ballClock p.1 r) p.2)
    (hfinite : ∀ᶠ i in l, ballClock (F i).1 (F i).2 ≠ ⊤)
    (hne : p.2 ≠ dist (p.1 0) 0) :
    Tendsto (fun i => IntervalReparamEDist.intervalEDist (F i).1 p.1
      (ballClock (F i).1 (F i).2) (ballClock p.1 p.2)) l (𝓝 0) := by
  have hlimfin : ballClock p.1 p.2 ≠ ⊤ := ballClock_ne_top ⟨p.1, hunb⟩ p.2
  have hpath : Tendsto (fun i => (F i).1) l (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hF
  have heval : Tendsto (fun i => (F i).1 0) l (𝓝 (p.1 0)) :=
    (continuous_eval_const 0).tendsto p.1 |>.comp hpath
  rcases lt_or_gt_of_ne hne with hsmall | hlarge
  · have hz : ballClock p.1 p.2 = 0 := by
      apply openExitTime_eq_zero_of_not_mem
      simpa only [mem_ball, not_lt] using le_of_lt hsmall
    have hevent : ∀ᶠ i in l, (F i).2 < dist ((F i).1 0) 0 := by
      have hd := (continuous_snd.tendsto p).comp hF
      exact hd.eventually_lt (heval.dist tendsto_const_nhds) hsmall
    have hdist : Tendsto (fun i => edist ((F i).1 0) (p.1 0)) l (𝓝 0) := by
      simpa only [edist_self] using heval.edist (tendsto_const_nhds :
        Tendsto (fun _ : α => p.1 0) l (𝓝 (p.1 0)))
    apply hdist.congr'
    filter_upwards [hevent] with i hi
    have hi0 : ballClock (F i).1 (F i).2 = 0 := by
      apply openExitTime_eq_zero_of_not_mem
      simpa only [mem_ball, not_lt] using le_of_lt hi
    rw [hi0, hz, IntervalReparamEDist.intervalEDist_zero_zero]
  · have hpos : 0 < (ballClock p.1 p.2).toNNReal := by
      apply pos_iff_ne_zero.mpr
      intro hzero
      have hout := openExitTime_not_mem (B := fun t (f : Path d) => f t)
        (ω := p.1) (isOpen_ball : IsOpen (ball (0 : EuclideanSpace ℝ (Fin d)) p.2))
        p.1.continuous hlimfin
      change p.1 (ballClock p.1 p.2).toNNReal ∉ ball 0 p.2 at hout
      apply hout
      simpa only [hzero, mem_ball] using hlarge
    have hclock := tendsto_ballClock_of_continuousAt_radius hF hunb hc
    have hclock' := (ENNReal.tendsto_toNNReal hlimfin).comp hclock
    have hpair : Tendsto (fun i => ((F i).1, (ballClock (F i).1 (F i).2).toNNReal)) l
        (𝓝 (p.1, (ballClock p.1 p.2).toNNReal)) := hpath.prodMk_nhds hclock'
    have hdist := IntervalReparamEDist.tendsto_intervalEDist_of_positive_duration hpair hpos
    apply hdist.congr'
    filter_upwards [hfinite] with i hi
    simp only [ENNReal.coe_toNNReal hi, ENNReal.coe_toNNReal hlimfin]

end LatticeProb.UnboundedRayIntervalIntegrand
