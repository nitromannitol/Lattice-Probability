import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.SetSemiring

/-! # Disjointification and symmetric-difference error -/

set_option autoImplicit false

open Set MeasureTheory
open scoped symmDiff BigOperators

namespace LatticeProb

variable {α ι : Type*} [PartialOrder ι] [LocallyFiniteOrderBot ι]

/-- Disjointification introduces errors only where the original families differ. -/
theorem disjointed_symmDiff_subset (s t : ι → Set α) (i : ι) :
    disjointed s i ∆ disjointed t i ⊆ ⋃ j, s j ∆ t j := by
  classical
  intro x hx
  by_contra h
  have heq : ∀ j, x ∈ s j ↔ x ∈ t j := by
    intro j
    have hj : x ∉ s j ∆ t j := by
      intro hj
      exact h (mem_iUnion.mpr ⟨j, hj⟩)
    simp only [mem_symmDiff, not_or, not_and] at hj
    exact ⟨fun hs => by_contra fun ht => hj.1 hs ht,
      fun ht => by_contra fun hs => hj.2 ht hs⟩
  have hd : x ∈ disjointed s i ↔ x ∈ disjointed t i := by
    simp only [disjointed_eq_inter_compl, mem_inter_iff, mem_iInter, mem_compl_iff]
    simp only [heq]
  simp only [mem_symmDiff] at hx
  tauto

variable [MeasurableSpace α] [Fintype ι]

/-- Disjointifying approximants to a disjoint family costs at most the sum of their errors. -/
theorem measure_symmDiff_disjointed_le (μ : Measure α) (s t : ι → Set α)
    (hs : Pairwise (Function.onFun Disjoint s)) (i : ι) :
    μ (s i ∆ disjointed t i) ≤ ∑ j, μ (s j ∆ t j) := by
  have hsi : disjointed s i = s i := disjointed_eq_self fun j hj => hs (ne_of_lt hj)
  calc
    μ (s i ∆ disjointed t i) = μ (disjointed s i ∆ disjointed t i) := by rw [hsi]
    _ ≤ μ (⋃ j, s j ∆ t j) := measure_mono (disjointed_symmDiff_subset s t i)
    _ ≤ ∑ j, μ (s j ∆ t j) := measure_iUnion_fintype_le μ _

end LatticeProb
