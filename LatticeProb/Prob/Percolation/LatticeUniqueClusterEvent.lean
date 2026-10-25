import LatticeProb.Prob.Percolation.LatticeUniqueCluster

/-!
# The measurable unique infinite component event

Existence and uniqueness of an infinite actual component have a countable vertex
characterization. On this good event, membership in the selected support is measurable.
No probability-one assertion or external percolation uniqueness theorem is assumed.
-/

namespace LatticeProb.Percolation

open MeasureTheory

variable {d : ℕ}

/-- The event of existence and uniqueness of an infinite actual open component. -/
def uniqueInfiniteComponentEvent (d : ℕ) : Set (Configuration d) :=
  {ω | HasUniqueInfiniteOpenComponent ω}

/-- The literal uniqueness event is exactly its countable vertex characterization. -/
theorem mem_uniqueInfiniteComponentEvent_iff (ω : Configuration d) :
    ω ∈ uniqueInfiniteComponentEvent d ↔
      (∃ x, ω ∈ infiniteComponentEvent x) ∧
      ∀ x y, ω ∈ infiniteComponentEvent x → ω ∈ infiniteComponentEvent y →
        (openGraph ω).Reachable x y :=
  hasUniqueInfiniteOpenComponent_iff_vertices ω

/-- Uniqueness is measurable by countable existence and pairwise reachability of vertices. -/
theorem measurableSet_uniqueInfiniteComponentEvent (d : ℕ) :
    MeasurableSet (uniqueInfiniteComponentEvent d) := by
  have heq : uniqueInfiniteComponentEvent d =
      (⋃ x : Vertex d, infiniteComponentEvent x) ∩
      ⋂ x : Vertex d, ⋂ y : Vertex d,
        ((infiniteComponentEvent x)ᶜ ∪ (infiniteComponentEvent y)ᶜ ∪
          {ω : Configuration d | (openGraph ω).Reachable x y}) := by
    ext ω
    simp only [mem_uniqueInfiniteComponentEvent_iff, Set.mem_inter_iff, Set.mem_iUnion,
      Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hex, hr⟩
      refine ⟨hex, fun x y => ?_⟩
      by_cases hx : ω ∈ infiniteComponentEvent x
      · by_cases hy : ω ∈ infiniteComponentEvent y
        · exact Or.inr (hr x y hx hy)
        · exact Or.inl (Or.inr hy)
      · exact Or.inl (Or.inl hx)
    · rintro ⟨hex, hr⟩
      refine ⟨hex, fun x y hx hy => ?_⟩
      rcases hr x y with (hnx | hny) | hxy
      · exact (hnx hx).elim
      · exact (hny hy).elim
      · exact hxy
  rw [heq]
  refine (MeasurableSet.iUnion measurableSet_infiniteComponentEvent).inter ?_
  exact MeasurableSet.iInter (fun x => MeasurableSet.iInter (fun y =>
    ((measurableSet_infiniteComponentEvent x).compl.union
      (measurableSet_infiniteComponentEvent y).compl).union
      (measurableSet_openGraph_reachable x y)))

/-- On the good-event subtype, membership in the selected actual support is measurable. -/
theorem measurableSet_mem_uniqueInfiniteComponent (x : Vertex d) :
    MeasurableSet {ω : uniqueInfiniteComponentEvent d |
      x ∈ (uniqueInfiniteComponent ω.property).supp} := by
  have heq : {ω : uniqueInfiniteComponentEvent d |
      x ∈ (uniqueInfiniteComponent ω.property).supp} =
      Subtype.val ⁻¹' infiniteComponentEvent x := by
    ext ω
    exact mem_uniqueInfiniteComponent_iff ω.property x
  rw [heq]
  exact (measurableSet_infiniteComponentEvent x).preimage measurable_subtype_coe

/-- The fully open positive-dimensional lattice belongs to the literal measurable good event. -/
theorem allOpen_mem_uniqueInfiniteComponentEvent (d : ℕ) [NeZero d] :
    allOpen d ∈ uniqueInfiniteComponentEvent d :=
  allOpen_hasUniqueInfiniteOpenComponent d

end LatticeProb.Percolation
