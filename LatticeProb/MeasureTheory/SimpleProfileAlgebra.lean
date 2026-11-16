import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.SetAlgebra

/-! # Simple functions with fibres in a set algebra -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A constant simple function has its values and attained fibres in any prescribed
value set and set algebra containing its value. -/
theorem simpleFunc_const_range_fibres {α E : Type*} [MeasurableSpace α]
    {D : Set E} {𝒜 : Set (Set α)} (h𝒜 : IsSetAlgebra 𝒜) {y : E} (hy : y ∈ D) :
    Set.range (SimpleFunc.const α y) ⊆ D ∧
      ∀ z ∈ Set.range (SimpleFunc.const α y),
        (SimpleFunc.const α y) ⁻¹' {z} ∈ 𝒜 := by
  constructor
  · rintro z ⟨x, rfl⟩
    exact hy
  · rintro z ⟨x, rfl⟩
    change (SimpleFunc.const α y) ⁻¹' {y} ∈ 𝒜
    have he : (SimpleFunc.const α y) ⁻¹' {y} = Set.univ := by
      ext x
      simp [SimpleFunc.const]
    rw [he]
    exact h𝒜.univ_mem

/-- Combining two simple functions along an algebra set preserves prescribed values
and algebraic fibres. -/
theorem simpleFunc_piecewise_range_fibres {α E : Type*} [MeasurableSpace α]
    {D : Set E} {𝒜 : Set (Set α)} (h𝒜 : IsSetAlgebra 𝒜)
    {s : Set α} (hs : s ∈ 𝒜) (hsm : MeasurableSet s) (f g : SimpleFunc α E)
    (hf : Set.range f ⊆ D ∧ ∀ y ∈ Set.range f, f ⁻¹' {y} ∈ 𝒜)
    (hg : Set.range g ⊆ D ∧ ∀ y ∈ Set.range g, g ⁻¹' {y} ∈ 𝒜) :
    Set.range (SimpleFunc.piecewise s hsm f g) ⊆ D ∧
      ∀ y ∈ Set.range (SimpleFunc.piecewise s hsm f g),
        (SimpleFunc.piecewise s hsm f g) ⁻¹' {y} ∈ 𝒜 := by
  classical
  have fibres (u : SimpleFunc α E)
      (hu : ∀ y ∈ Set.range u, u ⁻¹' {y} ∈ 𝒜) (y : E) : u ⁻¹' {y} ∈ 𝒜 := by
    by_cases hy : y ∈ Set.range u
    · exact hu y hy
    · have he : u ⁻¹' {y} = ∅ := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
        intro hx
        exact hy ⟨x, hx⟩
      rw [he]
      exact h𝒜.empty_mem
  constructor
  · rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ s
    · simpa [SimpleFunc.piecewise_apply, hx] using hf.1 ⟨x, rfl⟩
    · simpa [SimpleFunc.piecewise_apply, hx] using hg.1 ⟨x, rfl⟩
  · intro y _
    rw [SimpleFunc.coe_piecewise, Set.piecewise_preimage, Set.ite]
    exact h𝒜.union_mem (h𝒜.inter_mem (fibres f hf.2 y) hs)
      (h𝒜.inter_mem (fibres g hg.2 y) (h𝒜.compl_mem hs))

end LatticeProb
