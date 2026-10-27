import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent

namespace LatticeProb.Percolation

open MeasureTheory

variable {d : ℕ}

/-- Every property of the open graph induced on finitely many vertices is measurable. -/
theorem measurableSet_induced_openGraph (s : Finset (Vertex d))
    (P : SimpleGraph {x : Vertex d // x ∈ s} → Prop) :
    MeasurableSet {ω : Configuration d | P ((openGraph ω).induce (s : Set (Vertex d)))} := by
  classical
  let V := {x : Vertex d // x ∈ s}
  have hgraph (G : SimpleGraph V) :
      MeasurableSet {ω : Configuration d | (openGraph ω).induce (s : Set (Vertex d)) = G} := by
    have heq : {ω : Configuration d | (openGraph ω).induce (s : Set (Vertex d)) = G} =
        ⋂ x : V, ⋂ y : V, {ω | (openGraph ω).Adj x y ↔ G.Adj x y} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h x y
        rw [← h]
        rfl
      · intro h
        ext x y
        exact h x y
    rw [heq]
    refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
    by_cases h : G.Adj x y
    · simpa [h] using measurableSet_openGraph_adj (x : Vertex d) (y : Vertex d)
    · have hc : MeasurableSet {ω : Configuration d | ¬ (openGraph ω).Adj x y} :=
        (measurableSet_openGraph_adj (x : Vertex d) (y : Vertex d)).compl
      simpa [h] using hc
  have hfinite : Finite (SimpleGraph V) := Finite.of_injective SimpleGraph.Adj
    (fun _ _ h => SimpleGraph.ext h)
  have heq : {ω : Configuration d | P ((openGraph ω).induce (s : Set (Vertex d)))} =
      ⋃ G : SimpleGraph V, ⋃ (_ : P G),
        {ω : Configuration d | (openGraph ω).induce (s : Set (Vertex d)) = G} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨G, h, hG⟩
      simpa [hG] using h
  rw [heq]
  exact MeasurableSet.iUnion fun G => MeasurableSet.iUnion fun _ => hgraph G

end LatticeProb.Percolation
