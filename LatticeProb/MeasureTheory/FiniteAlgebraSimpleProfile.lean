import LatticeProb.MeasureTheory.SimpleProfileAlgebra

/-! # Simple functions on finite algebra partitions -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A finite disjoint family of measurable algebra sets can be labelled by values
in a prescribed set, using a default value outside the family. -/
theorem exists_simpleFunc_of_disjoint_algebra_sets {α E ι : Type*} [MeasurableSpace α]
    {𝒜 : Set (Set α)} (h𝒜 : IsSetAlgebra 𝒜) {D : Set E}
    (t : ι → Set α) (v : ι → E) (v₀ : E) (hv₀ : v₀ ∈ D)
    (ht : ∀ i, t i ∈ 𝒜) (htm : ∀ i, MeasurableSet (t i))
    (hv : ∀ i, v i ∈ D) (hdisj : Pairwise (Function.onFun Disjoint t))
    (I : Finset ι) :
    ∃ f : SimpleFunc α E, Set.range f ⊆ D ∧
      (∀ y ∈ Set.range f, f ⁻¹' {y} ∈ 𝒜) ∧
      (∀ i ∈ I, ∀ x ∈ t i, f x = v i) ∧
      (∀ x, (∀ i ∈ I, x ∉ t i) → f x = v₀) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨SimpleFunc.const α v₀, (simpleFunc_const_range_fibres h𝒜 hv₀).1,
      (simpleFunc_const_range_fibres h𝒜 hv₀).2, ?_, ?_⟩
    · simp
    · intro x hx
      rfl
  | @insert i I hi ih =>
    obtain ⟨g, hgD, hgA, hgval, hgdefault⟩ := ih
    let f := SimpleFunc.piecewise (t i) (htm i) (SimpleFunc.const α (v i)) g
    have hf := simpleFunc_piecewise_range_fibres h𝒜 (ht i) (htm i)
      (SimpleFunc.const α (v i)) g (simpleFunc_const_range_fibres h𝒜 (hv i)) ⟨hgD, hgA⟩
    refine ⟨f, hf.1, hf.2, ?_, ?_⟩
    · intro j hj x hx
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp [f, SimpleFunc.piecewise_apply, hx]
      · have hne : i ≠ j := by
          intro h
          subst j
          exact hi hj
        have hxi : x ∉ t i := fun hxi => (Set.disjoint_left.mp (hdisj hne)) hxi hx
        simpa [f, SimpleFunc.piecewise_apply, hxi] using hgval j hj x hx
    · intro x hx
      have hxi : x ∉ t i := hx i (Finset.mem_insert_self i I)
      have hxI : ∀ j ∈ I, x ∉ t j := fun j hj => hx j (Finset.mem_insert_of_mem hj)
      simpa [f, SimpleFunc.piecewise_apply, hxi] using hgdefault x hxI

end LatticeProb
