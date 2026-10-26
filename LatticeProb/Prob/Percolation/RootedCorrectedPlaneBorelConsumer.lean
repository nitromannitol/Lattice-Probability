import LatticeProb.Prob.Percolation.RootedCorrectedPlaneBorel
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurableConsumer

/-!
# A nonconstant member of the rooted corrected-plane Borel relation

The first coordinate on the fully open two-dimensional lattice is a corrected plane
on the actual component rooted at zero, with real slope given by the first basis vector.
Its values at zero and the first unit vertex give a concrete nonconstant member of the
jointly measurable relation, without any literature assumptions or selections.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory

/-- The existing coordinate corrected plane lives on the actual all-open root component. -/
theorem allOpen_root_component_coordinate_correctedPlane :
    IsCorrectedPlane ((openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2))
      (Pi.single 0 1) (fun x => (x.val (0 : Fin 2) : ℝ)) := by
  have hmem : (0 : Vertex 2) ∈
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp := by
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial
  have heq := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hmem
  rw [heq]
  exact allOpen_isCorrectedPlane_coordinate 2 0

/-- The all-open coordinate triple belongs to the literal normalized source relation. -/
theorem allOpen_coordinate_mem_rooted_correctedPlane :
    (allOpen 2, (Pi.single 0 1, fun x : Vertex 2 => (x (0 : Fin 2) : ℝ))) ∈
      {z : Configuration 2 × ((Fin 2 → ℝ) × (Vertex 2 → ℝ)) |
        z.2.2 0 = 0 ∧ IsCorrectedPlane ((openGraph z.1).connectedComponentMk 0) z.2.1
          (fun x => z.2.2 x.val)} := by
  exact ⟨by norm_num, allOpen_root_component_coordinate_correctedPlane⟩

/-- The Borel relation has an explicit normalized corrected-plane member whose restriction
has different values at the root and an actual neighboring component vertex. -/
theorem allOpen_rooted_correctedPlane_measurable_consumer :
    MeasurableSet {z : Configuration 2 × ((Fin 2 → ℝ) × (Vertex 2 → ℝ)) |
      z.2.2 0 = 0 ∧ IsCorrectedPlane ((openGraph z.1).connectedComponentMk 0) z.2.1
        (fun x => z.2.2 x.val)} ∧
    (allOpen 2, (Pi.single 0 1, fun x : Vertex 2 => (x (0 : Fin 2) : ℝ))) ∈
      {z : Configuration 2 × ((Fin 2 → ℝ) × (Vertex 2 → ℝ)) |
        z.2.2 0 = 0 ∧ IsCorrectedPlane ((openGraph z.1).connectedComponentMk 0) z.2.1
          (fun x => z.2.2 x.val)} ∧
    (let C := (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)
     ∃ o e : C, o.val = 0 ∧ e.val = unit (0 : Fin 2) ∧
       (o.val (0 : Fin 2) : ℝ) = 0 ∧ (e.val (0 : Fin 2) : ℝ) = 1 ∧
       (o.val (0 : Fin 2) : ℝ) ≠ (e.val (0 : Fin 2) : ℝ)) := by
  refine ⟨measurableSet_rooted_normalized_correctedPlane 0,
    allOpen_coordinate_mem_rooted_correctedPlane, ?_⟩
  dsimp only
  have hunit : unit (0 : Fin 2) ∈
      ((openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)).supp :=
    ((openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)).mem_supp_of_adj_mem_supp
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem allOpen_two_unit_adj
  refine ⟨⟨0, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩, ⟨unit 0, hunit⟩,
    rfl, rfl, ?_, ?_, ?_⟩
  · norm_num
  · norm_num [unit, Pi.single_apply]
  · norm_num [unit, Pi.single_apply]

end LatticeProb.Percolation
