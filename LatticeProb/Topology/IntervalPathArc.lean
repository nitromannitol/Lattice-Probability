import LatticeProb.Topology.MinimalGapSet
import LatticeProb.Topology.EqualGapCollapseContinuous
import LatticeProb.Topology.EqualGapCollapseFibres
import LatticeProb.Topology.ConvexFibreIntervalArc

/-! # Arcs in interval path images -/

set_option autoImplicit false

open Set
open scoped unitInterval

namespace LatticeProb

/-- A continuous image of a real interval contains an arc joining its distinct
endpoint images. -/
theorem exists_arc_in_interval_image {Y : Type*} [MetricSpace Y]
    (f : ℝ → Y) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hne : f a ≠ f b) :
    ∃ p : unitInterval → Y, Continuous p ∧ Function.Injective p ∧
      p 0 = f a ∧ p 1 = f b ∧ range p ⊆ f '' Icc a b := by
  classical
  obtain ⟨K, hsub, hclosed, ha, hb, hgap, hmin⟩ :=
    exists_minimal_closed_equal_gap f hf hab
  let G := equalGapCollapse f hclosed ha hb hgap
  let u : unitInterval → ℝ := fun t => a + (b - a) * (t : ℝ)
  have hu : Continuous u := by fun_prop
  have hmem (t : unitInterval) : u t ∈ Icc a b := by
    have ht : (0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 1 := t.property
    dsimp [u]
    constructor <;> nlinarith
  have hmono : Monotone u := by
    intro x y hxy
    have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
    dsimp [u]
    simpa only [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_left hxy' (sub_nonneg.mpr hab)) a)
  have hu0 : u 0 = a := by simp [u]
  have hu1 : u 1 = b := by simp [u]
  have hGa : G a = f a := equalGapCollapse_eq_of_mem f hclosed ha hb hgap ⟨le_rfl, hab⟩ ha
  have hGb : G b = f b := equalGapCollapse_eq_of_mem f hclosed ha hb hgap ⟨hab, le_rfl⟩ hb
  have hcont : Continuous (G ∘ u) := (continuous_equalGapCollapse f hclosed ha hb hgap hf).comp hu
  have hconv : ∀ x y z, x ≤ y → y ≤ z → (G ∘ u) x = (G ∘ u) z →
      (G ∘ u) y = (G ∘ u) x := by
    intro x y z hxy hyz heq
    exact equalGapCollapse_eq_of_between f hsub hclosed ha hb hgap hmin
      (hmem x) (hmem z) (hmono hxy) (hmono hyz) heq
  have hne' : (G ∘ u) 0 ≠ (G ∘ u) 1 := by simpa [Function.comp_def, hu0, hu1, hGa, hGb] using hne
  obtain ⟨p, hp, hpinj, hp0, hp1, hrange⟩ :=
    exists_arc_of_convex_fibres (G ∘ u) hcont hconv hne'
  refine ⟨p, hp, hpinj, ?_, ?_, ?_⟩
  · simpa [Function.comp_def, hu0, hGa] using hp0
  · simpa [Function.comp_def, hu1, hGb] using hp1
  · rw [hrange]
    rintro y ⟨t, rfl⟩
    obtain ⟨v, hv, w, hw, hvt, htw, hvw, hfree⟩ :=
      exists_equal_gap_bracketing_point f hclosed ha hb (hmem t) hgap
    exact ⟨v, hsub hv, (equalGapCollapse_eq_of_bracket f hclosed ha hb hgap
      (hmem t) hv hvt htw hvw hfree).symm⟩

end LatticeProb
