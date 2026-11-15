import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith

/-! # Radial gaps and restricted families -/

set_option autoImplicit false

namespace LatticeProb

open Set

/-- For nonempty sets, a gap in their distances to a point is equivalent to
constancy of the indices of sets meeting the concentric open balls. -/
theorem radial_gap_iff_restrictions_constant
    {ι E : Type*} [MetricSpace E] (C : ι → Set E) (hC : ∀ i, (C i).Nonempty)
    (z : E) {a b : ℝ} :
    (∀ i, Metric.infDist z (C i) ≤ a ∨ b ≤ Metric.infDist z (C i)) ↔
      ∀ r ∈ Ioo a b, ∀ s ∈ Ioo a b,
        {i | (C i ∩ Metric.ball z r).Nonempty} =
          {i | (C i ∩ Metric.ball z s).Nonempty} := by
  have hmem (i : ι) (r : ℝ) :
      (C i ∩ Metric.ball z r).Nonempty ↔ Metric.infDist z (C i) < r := by
    rw [Metric.infDist_lt_iff (hC i)]
    constructor
    · rintro ⟨x, hx, hball⟩
      exact ⟨x, hx, by simpa only [Metric.mem_ball, dist_comm] using hball⟩
    · rintro ⟨x, hx, hdist⟩
      exact ⟨x, hx, by simpa only [Metric.mem_ball, dist_comm] using hdist⟩
  constructor
  · intro h r hr s hs
    ext i
    simp only [mem_ofPred_eq, hmem]
    rcases h i with hi | hi <;> constructor <;> intro hval <;> linarith [hr.1, hr.2, hs.1, hs.2]
  · intro h i
    by_contra hn
    have hai : a < Metric.infDist z (C i) := lt_of_not_ge (fun hi => hn (Or.inl hi))
    have hib : Metric.infDist z (C i) < b := lt_of_not_ge (fun hi => hn (Or.inr hi))
    let r := (a + Metric.infDist z (C i)) / 2
    let s := (Metric.infDist z (C i) + b) / 2
    have hr : r ∈ Ioo a b := by dsimp [r]; constructor <;> linarith
    have hs : s ∈ Ioo a b := by dsimp [s]; constructor <;> linarith
    have heq := h r hr s hs
    have hsi : i ∈ {i | (C i ∩ Metric.ball z s).Nonempty} := by
      change (C i ∩ Metric.ball z s).Nonempty
      apply (hmem i s).2
      dsimp [s]
      linarith
    have hri : i ∈ {i | (C i ∩ Metric.ball z r).Nonempty} := heq.symm ▸ hsi
    have hlt := (hmem i r).1 hri
    dsimp [r] at hlt
    linarith

end LatticeProb
