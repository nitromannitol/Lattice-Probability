import LatticeProb.Topology.ProperFiberComponentTransfer
import LatticeProb.Topology.FrontierArcComponent

/-! # Shared frontier arcs under maps with the same fibres -/

set_option autoImplicit false

open Function Set Topology
open scoped unitInterval

namespace LatticeProb

/-- A homeomorphism preserves the existence of an injective path contained in
both frontiers. -/
theorem exists_shared_frontier_arc_image_iff
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) (A B : Set Y) :
    (∃ p : C(unitInterval, Z), Injective p ∧
      (∀ t, p t ∈ frontier (e '' A)) ∧ (∀ t, p t ∈ frontier (e '' B))) ↔
    (∃ p : C(unitInterval, Y), Injective p ∧
      (∀ t, p t ∈ frontier A) ∧ (∀ t, p t ∈ frontier B)) := by
  constructor
  · rintro ⟨p, hp, hA, hB⟩
    refine ⟨⟨fun t => e.symm (p t), e.symm.continuous.comp p.continuous⟩, e.symm.injective.comp hp, ?_, ?_⟩
    · intro t
      have h := hA t
      rw [← e.image_frontier] at h
      obtain ⟨x, hx, he⟩ := h
      simpa [← he] using hx
    · intro t
      have h := hB t
      rw [← e.image_frontier] at h
      obtain ⟨x, hx, he⟩ := h
      simpa [← he] using hx
  · rintro ⟨p, hp, hA, hB⟩
    refine ⟨⟨fun t => e (p t), e.continuous.comp p.continuous⟩, e.injective.comp hp, ?_, ?_⟩
    · intro t
      rw [← e.image_frontier]
      exact ⟨p t, hA t, rfl⟩
    · intro t
      rw [← e.image_frontier]
      exact ⟨p t, hB t, rfl⟩

/-- Proper surjections with identical fibres have shared frontier arcs for the
same pairs of parameter-set images. -/
theorem exists_shared_frontier_arc_of_proper_maps_same_fibers_iff
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfs : Surjective f) (hgs : Surjective g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) (A B : Set X) :
    (∃ p : C(unitInterval, Z), Injective p ∧
      (∀ t, p t ∈ frontier (g '' A)) ∧ (∀ t, p t ∈ frontier (g '' B))) ↔
    (∃ p : C(unitInterval, Y), Injective p ∧
      (∀ t, p t ∈ frontier (f '' A)) ∧ (∀ t, p t ∈ frontier (f '' B))) := by
  obtain ⟨e, he, _⟩ :=
    exists_homeomorph_of_proper_maps_same_fibers_components f g hf hg hfs hgs hfg
  have himage (S : Set X) : e '' (f '' S) = g '' S := by
    rw [image_image]
    exact image_congr (fun x _ => he x)
  simpa only [himage] using exists_shared_frontier_arc_image_iff e (f '' A) (f '' B)

end LatticeProb
