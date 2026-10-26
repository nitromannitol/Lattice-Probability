import LatticeProb.Prob.Percolation.RootedHarmonicMeasurable
import LatticeProb.Prob.Percolation.CorrectedPlaneConsumer

/-!
# A nonconstant member of the rooted harmonic relation

On the fully open two-dimensional lattice, the first coordinate vanishes at the root
and is harmonic on its actual component. It equals one at the first unit vertex, so the
measurable rooted harmonic relation has a concrete nonconstant member.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open MeasureTheory

/-- The first coordinate is harmonic on the actual all-open component rooted at zero. -/
theorem allOpen_root_component_coordinate_harmonic
    (x : (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)) :
    componentLaplacian ((openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2))
      (fun y => (y.val (0 : Fin 2) : ℝ)) x = 0 := by
  have hmem : (0 : Vertex 2) ∈
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp := by
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial
  have heq := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hmem
  revert x
  rw [heq]
  exact allOpen_component_coordinate_harmonic 2 0

/-- The all-open configuration paired with its first coordinate belongs to the literal
normalized rooted harmonic relation, with no inputs beyond the existing coordinate theorem. -/
theorem allOpen_coordinate_mem_rooted_harmonic :
    (allOpen 2, fun x : Vertex 2 => (x (0 : Fin 2) : ℝ)) ∈
      {z : Configuration 2 × (Vertex 2 → ℝ) |
        z.2 0 = 0 ∧ ∀ x, (openGraph z.1).Reachable 0 x →
          Graph.laplacian (openGraph z.1) z.2 x = 0} := by
  apply (rooted_normalized_harmonic_iff (allOpen 2) _ 0).mpr
  exact ⟨by norm_num, allOpen_root_component_coordinate_harmonic⟩

/-- The specialized relation and the Laplacian evaluation are measurable. Its coordinate
member restricts to a normalized harmonic function taking different values at actual vertices. -/
theorem allOpen_rooted_harmonic_measurable_consumer :
    Measurable (fun z : Configuration 2 × (Vertex 2 → ℝ) =>
      Graph.laplacian (openGraph z.1) z.2 0) ∧
    MeasurableSet {z : Configuration 2 × (Vertex 2 → ℝ) |
      z.2 0 = 0 ∧ ∀ x, (openGraph z.1).Reachable 0 x →
        Graph.laplacian (openGraph z.1) z.2 x = 0} ∧
    (let C := (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)
     ∃ o e : C, o.val = 0 ∧ e.val = unit (0 : Fin 2) ∧
       (o.val (0 : Fin 2) : ℝ) = 0 ∧ (e.val (0 : Fin 2) : ℝ) = 1 ∧
       ∀ x : C, componentLaplacian C (fun y => (y.val (0 : Fin 2) : ℝ)) x = 0) := by
  refine ⟨measurable_laplacian_openGraph 0,
    measurableSet_rooted_normalized_harmonic 0, ?_⟩
  dsimp only
  have hunit : unit (0 : Fin 2) ∈
      ((openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)).supp :=
    ((openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)).mem_supp_of_adj_mem_supp
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem allOpen_two_unit_adj
  refine ⟨⟨0, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩, ⟨unit 0, hunit⟩,
    rfl, rfl, ?_, ?_, allOpen_root_component_coordinate_harmonic⟩
  · norm_num
  · norm_num [unit, Pi.single_apply]

end LatticeProb.Percolation
