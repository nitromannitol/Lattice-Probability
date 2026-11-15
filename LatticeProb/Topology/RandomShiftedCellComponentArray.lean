import LatticeProb.Topology.RandomShiftedCellTwoComponentsEvent
import LatticeProb.Topology.RandomShiftedCellComponentEvent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Truncated component counts of shifted curve cells -/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

namespace LatticeProb

/-- The non-singleton connected components of a set. -/
def nonSingletonComponents {X : Type*} [TopologicalSpace X] (S : Set X) : Set (Set X) :=
  {C ∈ connectedComponentIn S '' S | ¬ C.Subsingleton}

/-- The number of non-singleton components, capped at two, including for infinite sets. -/
noncomputable def truncatedComponentCount {X : Type*} [TopologicalSpace X] (S : Set X) : ℕ := by
  classical
  exact (if (nonSingletonComponents S).Nonempty then 1 else 0) +
    (if ∃ C ∈ nonSingletonComponents S, ∃ D ∈ nonSingletonComponents S, C ≠ D then 1 else 0)

/-- Truncation equals the cardinality when there are at most two components. -/
theorem truncatedComponentCount_eq_ncard {X : Type*} [TopologicalSpace X] (S : Set X)
    (h : ∀ A ∈ nonSingletonComponents S, ∀ B ∈ nonSingletonComponents S,
      ∀ C ∈ nonSingletonComponents S, A ≠ B → A ≠ C → B ≠ C → False) :
    truncatedComponentCount S = (nonSingletonComponents S).ncard := by
  classical
  let T := nonSingletonComponents S
  change (if T.Nonempty then 1 else 0) +
    (if ∃ C ∈ T, ∃ D ∈ T, C ≠ D then 1 else 0) = T.ncard
  by_cases hT : T.Nonempty
  · obtain ⟨A, hA⟩ := hT
    by_cases htwo : ∃ B ∈ T, A ≠ B
    · obtain ⟨B, hB, hAB⟩ := htwo
      have hsub : T ⊆ {A, B} := by
        intro C hC
        simp only [mem_insert_iff, mem_singleton_iff]
        by_contra hn
        push Not at hn
        exact h A hA B hB C hC hAB (Ne.symm hn.1) (Ne.symm hn.2)
      have heq : T = {A, B} := subset_antisymm hsub (by
        intro C hC
        simp only [mem_insert_iff, mem_singleton_iff] at hC
        rcases hC with rfl | rfl <;> assumption)
      simp [heq, hAB]
    · have heq : T = {A} := subset_antisymm (by
        intro B hB
        simp only [mem_singleton_iff]
        by_contra hn
        exact htwo ⟨B, hB, Ne.symm hn⟩) (singleton_subset_iff.mpr hA)
      simp [heq]
  · have heq : T = ∅ := not_nonempty_iff_eq_empty.mp hT
    simp [heq]

/-- If no three non-singleton components occur, the truncated count agrees with
    the exact component cardinality simultaneously for all labelled cell pairs. -/
theorem shifted_cell_truncated_component_array_eq_ncard
    (η : C(ℝ, ℂ)) (ε θ : ℝ)
    (h : ∀ k l : ℤ,
      let S : Set ℂ := (shiftedCompactCell η ε θ k : Set ℂ) ∩ shiftedCompactCell η ε θ l
      ¬ ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
        connectedComponentIn S x ≠ connectedComponentIn S y ∧
        connectedComponentIn S x ≠ connectedComponentIn S z ∧
        connectedComponentIn S y ≠ connectedComponentIn S z ∧
        ¬ (connectedComponentIn S x).Subsingleton ∧
        ¬ (connectedComponentIn S y).Subsingleton ∧
        ¬ (connectedComponentIn S z).Subsingleton) :
    ∀ k l : ℤ,
      let S : Set ℂ := (shiftedCompactCell η ε θ k : Set ℂ) ∩ shiftedCompactCell η ε θ l
      truncatedComponentCount S = (nonSingletonComponents S).ncard := by
  intro k l
  apply truncatedComponentCount_eq_ncard
  rintro A ⟨⟨x, hx, rfl⟩, hA⟩ B ⟨⟨y, hy, rfl⟩, hB⟩ C ⟨⟨z, hz, rfl⟩, hC⟩ hAB hAC hBC
  exact h k l ⟨x, hx, y, hy, z, hz, hAB, hAC, hBC, hA, hB, hC⟩

/-- Almost-everywhere measurable truncated intersection counts for every integer pair. -/
theorem aemeasurable_shifted_cell_truncated_component_array
    {Ω : Type*} [MeasurableSpace Ω] (η : Ω → C(ℝ, ℂ)) (ε θ : Ω → ℝ)
    (hη : Measurable η) (hε : Measurable ε) (hθ : Measurable θ)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    AEMeasurable (fun ω (k l : ℤ) => truncatedComponentCount
      ((shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
        shiftedCompactCell (η ω) (ε ω) (θ ω) l)) μ := by
  classical
  apply AEMeasurable.of_eval
  intro k
  apply AEMeasurable.of_eval
  intro l
  let S : Ω → Set ℂ := fun ω => (shiftedCompactCell (η ω) (ε ω) (θ ω) k : Set ℂ) ∩
    shiftedCompactCell (η ω) (ε ω) (θ ω) l
  let A : Set Ω := {ω | (nonSingletonComponents (S ω)).Nonempty}
  let B : Set Ω := {ω | ∃ C ∈ nonSingletonComponents (S ω),
    ∃ D ∈ nonSingletonComponents (S ω), C ≠ D}
  have hA : NullMeasurableSet A μ := by
    simpa only [A, S, nonSingletonComponents, Set.Nonempty, mem_ofPred_eq, exists_prop] using
      nullMeasurableSet_random_shifted_cell_inter_component η ε θ k l hη hε hθ μ
  have hB : NullMeasurableSet B μ := by
    have heq : B = {ω : Ω | ∃ x ∈ S ω, ∃ y ∈ S ω,
        connectedComponentIn (S ω) x ≠ connectedComponentIn (S ω) y ∧
        ¬ (connectedComponentIn (S ω) x).Subsingleton ∧
        ¬ (connectedComponentIn (S ω) y).Subsingleton} := by
      ext ω
      simp only [B, nonSingletonComponents, mem_ofPred_eq, mem_image]
      constructor
      · rintro ⟨_, ⟨⟨x, hx, rfl⟩, hC⟩, _, ⟨⟨y, hy, rfl⟩, hD⟩, hne⟩
        exact ⟨x, hx, y, hy, hne, hC, hD⟩
      · rintro ⟨x, hx, y, hy, hne, hC, hD⟩
        exact ⟨_, ⟨⟨x, hx, rfl⟩, hC⟩, _, ⟨⟨y, hy, rfl⟩, hD⟩, hne⟩
    rw [heq]
    exact nullMeasurableSet_random_shifted_cell_inter_two_components η ε θ k l hη hε hθ μ
  have h1 : AEMeasurable (A.indicator (fun _ : Ω => (1 : ℕ))) μ :=
    aemeasurable_const.indicator₀ hA
  have h2 : AEMeasurable (B.indicator (fun _ : Ω => (1 : ℕ))) μ :=
    aemeasurable_const.indicator₀ hB
  convert h1.add h2 using 1
  funext ω
  simp [truncatedComponentCount, Set.indicator, A, B, S, Pi.add_apply]

end LatticeProb
