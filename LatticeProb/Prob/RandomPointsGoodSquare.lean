import LatticeProb.Prob.RandomPointsGoodCover

/-! # Square nets with two simultaneous point properties -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LatticeProb.RandomPointsCover

open LatticeProb.ParentBlock

/-- Uniformly over nondegenerate squares, a finite net can be chosen inside the
square satisfying two measurable properties when the sum of their bad-point
masses is sufficiently small. The number of points depends only on the relative
covering radius. -/
theorem exists_good_square_net (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (c : ℂ) (a : ℝ), 0 < a →
      ∀ G₁ G₂ : Set ℂ, MeasurableSet G₁ → MeasurableSet G₂ →
      ENNReal.ofReal δ + (N : ℝ≥0∞) *
        (volume[|closedSquare c a] G₁ᶜ + volume[|closedSquare c a] G₂ᶜ) < 1 →
      ∃ z : Fin N → ℂ, (∀ j, z j ∈ closedSquare c a ∧ z j ∈ G₁ ∧ z j ∈ G₂) ∧
        closedSquare c a ⊆ ⋃ j, ball (z j) (δ * a) := by
  obtain ⟨N₀, hN₀⟩ := exists_measure_pi_not_subset_iUnion_ball_le δ hδ
  refine ⟨N₀, fun N hN c a ha G₁ G₂ hG₁ hG₂ hsmall => ?_⟩
  let μ := volume[|closedSquare c a]
  let Q := closedSquare c a
  let : IsProbabilityMeasure μ := isProbabilityMeasure_cond_closedSquare c ha
  have hQ : MeasurableSet Q := (isClosed_closedSquare c a).measurableSet
  have hQzero : μ Qᶜ = 0 := by
    change volume[|Q] Qᶜ = 0
    rw [cond_apply hQ, Set.inter_compl_self, measure_empty, mul_zero]
  have hmass : μ (Q ∩ G₁ ∩ G₂)ᶜ ≤ μ G₁ᶜ + μ G₂ᶜ := by
    calc
      μ (Q ∩ G₁ ∩ G₂)ᶜ ≤ μ (Qᶜ ∪ (G₁ᶜ ∪ G₂ᶜ)) := by
        apply measure_mono
        intro x hx
        simp only [mem_compl_iff, mem_inter_iff, mem_union] at hx ⊢
        tauto
      _ ≤ μ Qᶜ + (μ G₁ᶜ + μ G₂ᶜ) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ = μ G₁ᶜ + μ G₂ᶜ := by rw [hQzero, zero_add]
  have hs : ENNReal.ofReal δ + (N : ℝ≥0∞) * μ (Q ∩ G₁ ∩ G₂)ᶜ < 1 :=
    lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_right hmass _)) hsmall
  obtain ⟨z, hz, hcover⟩ := exists_good_cover_of_failure_bound μ N Q (Q ∩ G₁ ∩ G₂)
    ((hQ.inter hG₁).inter hG₂) (δ * a) (ENNReal.ofReal δ) (hN₀ N hN c a ha) hs
  refine ⟨z, ?_, hcover⟩
  intro j
  exact ⟨(hz j).1.1, (hz j).1.2, (hz j).2⟩

end LatticeProb.RandomPointsCover
end
