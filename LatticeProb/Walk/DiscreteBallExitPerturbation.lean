import LatticeProb.Bonanno.BouRabeeGwynne.WalkAdaptiveStopping

/-! # Discrete ball exits under perturbations of vertex positions -/

set_option autoImplicit false

open Set Metric
open BouRabeeGwynne.FiniteConductanceNetwork

namespace LatticeProb

/-- Nearby vertex positions bracket a discrete ball exit by the exits from
balls with radii shifted by the position error. Infinite exits are included. -/
theorem discrete_ball_exit_sandwich_of_dist_le
    {V E : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [PseudoMetricSpace E] (p q : V → E) (ω : ℕ → V) (z : E) (r δ : ℝ)
    (hclose : ∀ v, dist (p v) (q v) ≤ δ) :
    exitTime (p ⁻¹' ball z (r - δ)) ω ≤ exitTime (q ⁻¹' ball z r) ω ∧
      exitTime (q ⁻¹' ball z r) ω ≤ exitTime (p ⁻¹' ball z (r + δ)) ω := by
  constructor
  · apply exitTime_le_of_subset _ ω
    intro v hv
    simp only [mem_preimage, mem_ball] at hv ⊢
    have h := dist_triangle (q v) (p v) z
    rw [dist_comm (q v) (p v)] at h
    linarith [hclose v]
  · apply exitTime_le_of_subset _ ω
    intro v hv
    simp only [mem_preimage, mem_ball] at hv ⊢
    linarith [dist_triangle (p v) (q v) z, hclose v]

/-- If the outer exit is finite and the reference path oscillates by at most η
between the neighboring-radius exits, the two discrete exit positions are
within η plus the position error. -/
theorem dist_discrete_ball_exit_le_of_oscillation
    {V E : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [PseudoMetricSpace E] (p q : V → E) (ω : ℕ → V) (z : E) (r δ η : ℝ)
    (hclose : ∀ v, dist (p v) (q v) ≤ δ)
    (hfinite : exitTime (p ⁻¹' ball z (r + δ)) ω ≠ ⊤)
    (hosc : ∀ i ∈ Icc ((exitTime (p ⁻¹' ball z (r - δ)) ω).untopD 0)
        ((exitTime (p ⁻¹' ball z (r + δ)) ω).untopD 0),
      ∀ j ∈ Icc ((exitTime (p ⁻¹' ball z (r - δ)) ω).untopD 0)
        ((exitTime (p ⁻¹' ball z (r + δ)) ω).untopD 0),
      dist (p (ω i)) (p (ω j)) ≤ η) :
    dist (p (ω ((exitTime (p ⁻¹' ball z r) ω).untopD 0)))
      (q (ω ((exitTime (q ⁻¹' ball z r) ω).untopD 0))) ≤ η + δ := by
  have hδ : 0 ≤ δ := (dist_nonneg : 0 ≤ dist (p (ω 0)) (q (ω 0))).trans (hclose (ω 0))
  have hp := discrete_ball_exit_sandwich_of_dist_le p p ω z r δ
    (fun v => by simpa only [dist_self] using hδ)
  have hq := discrete_ball_exit_sandwich_of_dist_le p q ω z r δ hclose
  have hpf : exitTime (p ⁻¹' ball z r) ω ≠ ⊤ := ne_top_of_le_ne_top hfinite hp.2
  have hqf : exitTime (q ⁻¹' ball z r) ω ≠ ⊤ := ne_top_of_le_ne_top hfinite hq.2
  have hp0 := WithTop.untopD_mono (a := 0) hpf hp.1
  have hp1 := WithTop.untopD_mono (a := 0) hfinite hp.2
  have hq0 := WithTop.untopD_mono (a := 0) hqf hq.1
  have hq1 := WithTop.untopD_mono (a := 0) hfinite hq.2
  have ho := hosc _ ⟨hp0, hp1⟩ _ ⟨hq0, hq1⟩
  linarith [dist_triangle (p (ω ((exitTime (p ⁻¹' ball z r) ω).untopD 0)))
    (p (ω ((exitTime (q ⁻¹' ball z r) ω).untopD 0)))
    (q (ω ((exitTime (q ⁻¹' ball z r) ω).untopD 0))),
    hclose (ω ((exitTime (q ⁻¹' ball z r) ω).untopD 0))]

end LatticeProb
