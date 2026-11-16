import LatticeProb.Topology.IntervalImagePointArc

/-! # Arcs in compact interval images -/

set_option autoImplicit false

open Set
open scoped unitInterval

namespace LatticeProb

/-- Any two distinct points in a continuous compact interval image are joined
by an arc contained in that image. -/
theorem exists_arc_between_points_in_compact_interval_image {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) {a b : ℝ} (hf : ContinuousOn f (Icc a b)) {x y : Y}
    (hx : x ∈ f '' Icc a b) (hy : y ∈ f '' Icc a b) (hne : x ≠ y) :
    ∃ p : unitInterval → Y, Continuous p ∧ Function.Injective p ∧
      p 0 = x ∧ p 1 = y ∧ range p ⊆ f '' Icc a b := by
  have hab : a ≤ b := by
    obtain ⟨u, hu, _⟩ := hx
    exact hu.1.trans hu.2
  let g : ℝ → Y := fun t => f (projIcc a b hab t)
  have hg : Continuous g :=
    (continuousOn_iff_continuous_domRestrict.mp hf).comp continuous_projIcc
  have heq : g '' Icc a b = f '' Icc a b := by
    apply image_congr
    intro t ht
    simp only [g, projIcc_of_mem hab ht]
  rw [← heq] at hx hy ⊢
  exact exists_arc_between_points_in_interval_image g hg hx hy hne

/-- A nontrivial compact interval image in two frontiers contains a shared arc. -/
theorem exists_shared_frontier_arc_of_compact_interval_image {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) {a b : ℝ} (hf : ContinuousOn f (Icc a b)) {A B : Set Y}
    (hA : f '' Icc a b ⊆ frontier A) (hB : f '' Icc a b ⊆ frontier B)
    {x y : Y} (hx : x ∈ f '' Icc a b) (hy : y ∈ f '' Icc a b) (hne : x ≠ y) :
    ∃ p : C(unitInterval, Y), Function.Injective p ∧
      (∀ t, p t ∈ frontier A) ∧ (∀ t, p t ∈ frontier B) := by
  obtain ⟨p, hp, hi, _, _, hr⟩ :=
    exists_arc_between_points_in_compact_interval_image f hf hx hy hne
  exact ⟨⟨p, hp⟩, hi, fun t => hA (hr ⟨t, rfl⟩), fun t => hB (hr ⟨t, rfl⟩)⟩

end LatticeProb
