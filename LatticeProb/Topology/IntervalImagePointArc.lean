import LatticeProb.Topology.IntervalPathArc

/-! # Arcs between points in interval images -/

set_option autoImplicit false

open Set
open scoped unitInterval

namespace LatticeProb

/-- Any two distinct points in a continuous interval image are joined by an
arc contained in that image. -/
theorem exists_arc_between_points_in_interval_image {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) (hf : Continuous f) {a b : ℝ} {x y : Y}
    (hx : x ∈ f '' Icc a b) (hy : y ∈ f '' Icc a b) (hne : x ≠ y) :
    ∃ p : unitInterval → Y, Continuous p ∧ Function.Injective p ∧
      p 0 = x ∧ p 1 = y ∧ range p ⊆ f '' Icc a b := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rcases le_total u v with huv | hvu
  · obtain ⟨p, hp, hi, h0, h1, hr⟩ := exists_arc_in_interval_image f hf huv hne
    exact ⟨p, hp, hi, h0, h1, hr.trans (image_mono (Icc_subset_Icc hu.1 hv.2))⟩
  · obtain ⟨p, hp, hi, h0, h1, hr⟩ := exists_arc_in_interval_image f hf hvu hne.symm
    refine ⟨p ∘ unitInterval.symm, hp.comp unitInterval.continuous_symm,
      hi.comp unitInterval.symm_involutive.injective, ?_, ?_, ?_⟩
    · simpa only [Function.comp_apply, unitInterval.symm_zero] using h1
    · simpa only [Function.comp_apply, unitInterval.symm_one] using h0
    · rintro z ⟨t, rfl⟩
      exact image_mono (Icc_subset_Icc hv.1 hu.2) (hr ⟨unitInterval.symm t, rfl⟩)

/-- A nontrivial interval image contained in two frontiers contains a shared arc. -/
theorem exists_shared_frontier_arc_of_interval_image {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) (hf : Continuous f) {a b : ℝ} {A B : Set Y}
    (hA : f '' Icc a b ⊆ frontier A) (hB : f '' Icc a b ⊆ frontier B)
    {x y : Y} (hx : x ∈ f '' Icc a b) (hy : y ∈ f '' Icc a b) (hne : x ≠ y) :
    ∃ p : C(unitInterval, Y), Function.Injective p ∧
      (∀ t, p t ∈ frontier A) ∧ (∀ t, p t ∈ frontier B) := by
  obtain ⟨p, hp, hi, _, _, hr⟩ := exists_arc_between_points_in_interval_image f hf hx hy hne
  exact ⟨⟨p, hp⟩, hi, fun t => hA (hr ⟨t, rfl⟩), fun t => hB (hr ⟨t, rfl⟩)⟩

end LatticeProb
