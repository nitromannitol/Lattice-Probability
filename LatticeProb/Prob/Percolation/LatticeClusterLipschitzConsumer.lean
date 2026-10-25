import LatticeProb.Prob.Percolation.LatticeClusterLipschitz
import LatticeProb.Prob.Percolation.LatticeClusterBall
import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent

/-!
# Actual cluster consumers of the edge characterization

Every coordinate restricted to any open component is Lipschitz, by checking its open edges.
On the infinite all-open two-dimensional component a coordinate is nonconstant. In the
all-closed configuration every function on the actual singleton component is Lipschitz.
-/

namespace LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- Each coordinate changes by at most one across an actual open edge of a component. -/
theorem component_coordinate_edge_bound (C : OpenComponent ω) (i : Fin d)
    (x y : C) (hxy : (componentGraph C).Adj x y) :
    |(x.val i : ℝ) - (y.val i : ℝ)| ≤ 1 := by
  have hsum := lattice_adj_iff_l1Dist.mp (openGraph_le ω hxy)
  have hi : |x.val i - y.val i| ≤ (1 : ℤ) := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x.val j - y.val j))
      (Finset.mem_univ i)
  exact_mod_cast hi

/-- A coordinate on any actual component satisfies the global graph-distance bound with one. -/
theorem component_coordinate_dist_bound (C : OpenComponent ω) (i : Fin d) :
    ∀ x y : C, |(x.val i : ℝ) - (y.val i : ℝ)| ≤
      1 * ((componentGraph C).dist x y : ℝ) :=
  (component_dist_bound_iff_edge_bound C (fun x => (x.val i : ℝ)) 1).mpr
    (fun x y hxy => component_coordinate_edge_bound C i x y hxy)

/-- The edge characterization proves genuine source Lipschitzness of restricted coordinates. -/
theorem componentLipschitz_coordinate (C : OpenComponent ω) (i : Fin d) :
    ComponentLipschitz C (fun x => (x.val i : ℝ)) :=
  ⟨1, zero_le_one, component_coordinate_dist_bound C i⟩

/-- Every function on an actual all-closed singleton component is Lipschitz with bound zero. -/
theorem allClosed_componentLipschitz (z : Vertex d)
    (u : ((openGraph (allClosed d)).connectedComponentMk z) → ℝ) :
    ComponentLipschitz ((openGraph (allClosed d)).connectedComponentMk z) u := by
  refine ⟨0, le_refl _, ?_⟩
  intro x y
  have hxy : x = y := Subtype.ext
    ((allClosed_component_vertex_eq z x).trans (allClosed_component_vertex_eq z y).symm)
  subst y
  simp only [sub_self, abs_zero, zero_mul, le_refl]

/-- The actual all-open component at zero is infinite and has a nonconstant Lipschitz coordinate.
The global estimate here is obtained from the preceding open-edge bound, without harmonicity. -/
theorem allOpen_two_nonconstant_lipschitz :
    ∃ C : OpenComponent (allOpen 2), C.supp.Infinite ∧
      ∃ u : C → ℝ, ComponentLipschitz C u ∧ ∃ x y : C, u x ≠ u y := by
  let C : OpenComponent (allOpen 2) := (openGraph (allOpen 2)).connectedComponentMk 0
  have hzero : (0 : Vertex 2) ∈ C.supp := rfl
  have hunit : unit (0 : Fin 2) ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp hzero allOpen_two_unit_adj
  refine ⟨C, allOpen_mem_infiniteComponentEvent 0,
    (fun x => (x.val (0 : Fin 2) : ℝ)), componentLipschitz_coordinate C 0,
    ⟨0, hzero⟩, ⟨unit 0, hunit⟩, ?_⟩
  norm_num [unit, Pi.single_apply]

end LatticeProb.Percolation
