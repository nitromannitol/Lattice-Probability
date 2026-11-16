import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Data.Set.Countable

/-! # Countable families of simple functions -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Simple functions with values and attained level sets in fixed countable families
form a countable family. -/
theorem countable_simpleFunc_of_range_fibres {α E : Type*} [MeasurableSpace α]
    {D : Set E} {𝒜 : Set (Set α)} (hD : D.Countable) (h𝒜 : 𝒜.Countable) :
    {f : SimpleFunc α E | Set.range f ⊆ D ∧
      ∀ y ∈ Set.range f, f ⁻¹' {y} ∈ 𝒜}.Countable := by
  classical
  let code : SimpleFunc α E → Set (E × Set α) := fun f =>
    (fun y => (y, f ⁻¹' {y})) '' Set.range f
  have hinj : Function.Injective code := by
    intro f g hfg
    apply SimpleFunc.ext
    intro x
    have hmem : (f x, f ⁻¹' {f x}) ∈ code g := by
      rw [← hfg]
      exact ⟨f x, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, _, hy⟩ := hmem
    have hy₁ : y = f x := congrArg Prod.fst hy
    have hy₂ : g ⁻¹' {y} = f ⁻¹' {f x} := congrArg Prod.snd hy
    have hx : x ∈ g ⁻¹' {y} := by
      rw [hy₂]
      simp
    simpa only [mem_preimage, mem_singleton_iff, hy₁] using hx.symm
  apply (countable_ofPred_finite_subset (hD.prod h𝒜)).preimage hinj |>.mono
  intro f hf
  refine ⟨f.finite_range.image _, ?_⟩
  rintro p ⟨z, hz, rfl⟩
  exact ⟨hf.1 hz, hf.2 z hz⟩

end LatticeProb
