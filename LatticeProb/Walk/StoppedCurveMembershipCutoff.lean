import LatticeProb.Walk.StoppedCurveMembershipComparison

/-! # Finite-time estimates for stopped-curve membership disagreements -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory BouRabeeGwynne
open scoped ENNReal NNReal

namespace LatticeProb

/-- Disagreement before the reference exit is controlled by finitely many
one-time disagreement events and the reference exit tail. The exit vertex is
included, and the estimate also covers an infinite exit time. -/
theorem measure_membership_disagreement_le_cutoff {V : Type*} [MeasurableSpace V]
    (A B : Set V) (μ : Measure (ℕ → V)) (N : ℕ) :
    μ {ω | ∃ n : ℕ, (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime B ω ∧
      ¬ (ω n ∈ A ↔ ω n ∈ B)} ≤
      μ {ω | (N : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime B ω} +
        ∑ n ∈ Finset.range N, μ {ω | (n : WithTop ℕ) ≤
          FiniteConductanceNetwork.exitTime B ω ∧ ¬ (ω n ∈ A ↔ ω n ∈ B)} := by
  let T : Set (ℕ → V) := {ω | (N : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime B ω}
  let E : ℕ → Set (ℕ → V) := fun n => {ω | (n : WithTop ℕ) ≤
    FiniteConductanceNetwork.exitTime B ω ∧ ¬ (ω n ∈ A ↔ ω n ∈ B)}
  have hsub : {ω | ∃ n : ℕ, (n : WithTop ℕ) ≤ FiniteConductanceNetwork.exitTime B ω ∧
      ¬ (ω n ∈ A ↔ ω n ∈ B)} ⊆ T ∪ ⋃ n ∈ Finset.range N, E n := by
    intro ω hω
    obtain ⟨n, hn, hdiff⟩ := hω
    by_cases h : n < N
    · exact Or.inr (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_range.mpr h, ⟨hn, hdiff⟩⟩⟩)
    · exact Or.inl (le_trans (WithTop.coe_le_coe.mpr (Nat.le_of_not_gt h)) hn)
  calc
    _ ≤ μ (T ∪ ⋃ n ∈ Finset.range N, E n) := measure_mono hsub
    _ ≤ μ T + μ (⋃ n ∈ Finset.range N, E n) := measure_union_le _ _
    _ ≤ μ T + ∑ n ∈ Finset.range N, μ (E n) :=
      add_le_add_right (measure_biUnion_finset_le _ _) _

/-- Finite-time disagreement probabilities and an exit-tail bound imply a
stopped-curve law comparison for two uniformly close representatives. -/
theorem levyProkhorov_stoppedCurve_le_of_membership_cutoff {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (p q : V → Euc d) (U : Set (Euc d)) (μ : Measure (ℕ → V))
    (δ : ℝ) (r : ℝ≥0) (hδ : ∀ v, dist (p v) (q v) ≤ δ)
    (hδr : δ < (r : ℝ)) (N : ℕ)
    (hbound : μ {ω | (N : WithTop ℕ) ≤
      FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω} +
      ∑ n ∈ Finset.range N, μ {ω | (n : WithTop ℕ) ≤
        FiniteConductanceNetwork.exitTime (q ⁻¹' U) ω ∧
          ¬ (p (ω n) ∈ U ↔ q (ω n) ∈ U)} ≤ (r : ℝ≥0∞)) :
    levyProkhorovEDist
      (μ.map (stoppedPolygonalCurve p (p ⁻¹' U)))
      (μ.map (stoppedPolygonalCurve q (q ⁻¹' U))) ≤ r := by
  apply levyProkhorov_stoppedCurve_le_of_membership_disagreement p q U μ δ r hδ hδr
  exact (measure_membership_disagreement_le_cutoff (p ⁻¹' U) (q ⁻¹' U) μ N).trans hbound

end LatticeProb
end
