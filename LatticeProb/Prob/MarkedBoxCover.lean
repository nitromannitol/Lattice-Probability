import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.MeasuredSets

/-! Countable covers by measurable marks and finite products of spanning sets. -/

open Set MeasurableSpace MeasureTheory

namespace LatticeProb

/-- Measurable marks and finite-coordinate boxes from countably spanning
families admit a countable subfamily covering the whole product. -/
theorem exists_countable_cover_marked_boxes {E ι : Type*} {α : ι → Type*}
    [MeasurableSpace E] [Finite ι] {C : ∀ i, Set (Set (α i))}
    (hC : ∀ i, IsCountablySpanning (C i)) :
    ∃ D : Set (Set (E × (∀ i, α i))), D.Countable ∧
      D ⊆ Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
        (Set.univ.pi '' Set.univ.pi C) ∧ ⋃₀ D = univ := by
  obtain ⟨s, hs, hcover⟩ := (isCountablySpanning_measurableSet (α := E)).prod
    (IsCountablySpanning.pi hC)
  refine ⟨Set.range s, Set.countable_range _, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact hs n
  · simpa only [Set.sUnion_range] using hcover

/-- The covering family of marked boxes also covers modulo any measure. -/
theorem exists_countable_cover_marked_boxes_ae {E ι : Type*} {α : ι → Type*}
    [MeasurableSpace E] [∀ i, MeasurableSpace (α i)] [Finite ι]
    {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsCountablySpanning (C i))
    (μ : Measure (E × (∀ i, α i))) :
    ∃ D : Set (Set (E × (∀ i, α i))), D.Countable ∧
      D ⊆ Set.image2 (· ×ˢ ·) {s : Set E | MeasurableSet s}
        (Set.univ.pi '' Set.univ.pi C) ∧ μ (⋃₀ D)ᶜ = 0 := by
  obtain ⟨D, hD, hDC, hcover⟩ := exists_countable_cover_marked_boxes (E := E) hC
  exact ⟨D, hD, hDC, by simp [hcover]⟩

end LatticeProb
