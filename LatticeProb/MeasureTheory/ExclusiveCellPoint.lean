import Mathlib.MeasureTheory.Measure.AEDisjoint

/-! # Exclusive points of almost disjoint cells -/

set_option autoImplicit false

open MeasureTheory Set Function

namespace LatticeProb

/-- A positive-measure member of a countable family with null pairwise overlaps
contains a point belonging to no other member. -/
theorem exists_mem_only_of_pairwise_ae_disjoint
    {α ι : Type*} [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (C : ι → Set α) (hdisj : Pairwise (AEDisjoint μ on C))
    (i : ι) (hpos : 0 < μ (C i)) :
    ∃ x ∈ C i, ∀ j, x ∈ C j → j = i := by
  classical
  have hnull : μ (⋃ j : {j // j ≠ i}, C i ∩ C j) = 0 :=
    measure_iUnion_null fun j => hdisj (Ne.symm j.property)
  by_contra h
  push Not at h
  have hsub : C i ⊆ ⋃ j : {j // j ≠ i}, C i ∩ C j := by
    intro x hx
    obtain ⟨j, hj, hji⟩ := h x hx
    exact mem_iUnion.mpr ⟨⟨j, hji⟩, hx, hj⟩
  exact (ne_of_gt hpos) (measure_mono_null hsub hnull)

end LatticeProb
