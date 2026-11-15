import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Probability

/-! # Finite cutoffs for random families of events -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A bad event at a random index is controlled by the chance that the index
set escapes a deterministic finite cutoff and by the finite union bound. No
independence or measurability of the random set or the events is needed. -/
theorem measure_exists_mem_random_set_le_cutoff {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → Set ι) (S : Finset ι) (B : ι → Set Ω) (p : ℝ≥0∞)
    (hB : ∀ i ∈ S, μ (B i) ≤ p) :
    μ {ω | ∃ i ∈ K ω, ω ∈ B i} ≤
      μ {ω | ¬ K ω ⊆ (S : Set ι)} + (S.card : ℝ≥0∞) * p := by
  classical
  have hsub : {ω | ∃ i ∈ K ω, ω ∈ B i} ⊆
      {ω | ¬ K ω ⊆ (S : Set ι)} ∪ (⋃ i ∈ S, B i) := by
    intro ω hω
    by_cases hK : K ω ⊆ (S : Set ι)
    · right
      obtain ⟨i, hi, hbad⟩ := hω
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hK hi, hbad⟩⟩
    · exact Or.inl hK
  calc
    μ {ω | ∃ i ∈ K ω, ω ∈ B i} ≤
        μ ({ω | ¬ K ω ⊆ (S : Set ι)} ∪ (⋃ i ∈ S, B i)) := measure_mono hsub
    _ ≤ μ {ω | ¬ K ω ⊆ (S : Set ι)} + μ (⋃ i ∈ S, B i) := measure_union_le _ _
    _ ≤ μ {ω | ¬ K ω ⊆ (S : Set ι)} + (S.card : ℝ≥0∞) * p :=
      add_le_add_right (MatedCRTHarmonic.GMS4.finite_union_measure_le_card_mul μ S B p hB) _

end LatticeProb
