/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Geometry.BoundaryAnchoring at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Geometry
import LatticeProb.Bonanno.ReflectedGMS.Environment.UncoveredFacts
import LatticeProb.Bonanno.ReflectedGMS.Analysis.AnchoredEnergy
import LatticeProb.Bonanno.ReflectedGMS.Graph.Restriction

/-!
# Boundary anchoring

Every cell meeting a bounded planar set can reach a cell meeting its spatial
frontier by a finite walk supported on cells meeting the set.  The proof uses
only connected cell carriers, the covering clause (in the form: the uncovered
set is `H¹`-null, so some cell meets the complement of any ball containing the
set), global graph connectedness, and the intersection of adjacent cells.
-/

set_option autoImplicit false

open Set

namespace ReflectedGMS

/-- The closed axis-aligned rectangle with opposite corners. The order on the
Euclidean plane is coordinatewise. -/
def axisAlignedRectangle (a b : Plane) : Set Plane :=
  {z | ∀ i : Fin 2, a i ≤ z i ∧ z i ≤ b i}

/-- A closed axis-aligned rectangle is bounded. -/
lemma axisAlignedRectangle_isBounded (a b : Plane) :
    Bornology.IsBounded (axisAlignedRectangle a b) := by
  have hcompact : IsCompact
      (Set.pi Set.univ fun i : Fin 2 => Set.Icc (a i) (b i)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  let e : (Fin 2 → ℝ) ≃ₜ Plane :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm
  apply (hcompact.image e.continuous).isBounded.subset
  intro z hz
  refine ⟨fun i => z i, ?_, ?_⟩
  · intro i _
    exact hz i
  · exact e.apply_symm_apply z

/-- A connected set which meets `Q` but avoids its frontier is contained in the
interior of `Q`. -/
lemma connected_subset_interior_of_inter_nonempty_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {s Q : Set X}
    (hs : IsConnected s) (hsQ : (s ∩ Q).Nonempty)
    (hsfrontier : Disjoint s (frontier Q)) :
    s ⊆ interior Q := by
  apply hs.isPreconnected.subset_left_of_subset_union
      isOpen_interior isOpen_interior
  · exact Set.disjoint_of_subset interior_subset interior_subset disjoint_compl_right
  · intro x hxs
    have hxfrontier : x ∉ frontier Q := fun hxQ ↦
      Set.disjoint_left.1 hsfrontier hxs hxQ
    have hxcompl : x ∈ (frontier Q)ᶜ := hxfrontier
    rwa [compl_frontier_eq_union_interior] at hxcompl
  · rcases hsQ with ⟨x, hxs, hxQ⟩
    refine ⟨x, hxs, (mem_interior_iff_notMem_frontier hxQ).2 ?_⟩
    exact fun hxfrontier ↦ Set.disjoint_left.1 hsfrontier hxs hxfrontier

/-- In a connected graph, if vertices in `S` are either boundary vertices or
interior vertices, every interior step stays in `S`, and some vertex is not
interior, then every vertex in `S` has a finite walk through `S` to `B`. -/
lemma connected_exists_walk_to_boundary_within
    {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {S I B : Set V}
    (hSI : S ⊆ B ∪ I)
    (hstep : ∀ ⦃v w⦄, v ∈ I → G.Adj v w → w ∈ S)
    (hout : ∃ z, z ∉ I) :
    ∀ v, v ∈ S →
      ∃ b, b ∈ B ∧ ∃ p : G.Walk v b, ∀ x ∈ p.support, x ∈ S := by
  rcases hout with ⟨z, hz⟩
  intro v hv
  rcases hG v z with ⟨p⟩
  let rec cut {u : V} (q : G.Walk u z) (hu : u ∈ S) :
      ∃ b, b ∈ B ∧ ∃ r : G.Walk u b, ∀ x ∈ r.support, x ∈ S := by
    by_cases huB : u ∈ B
    · exact ⟨u, huB, .nil, by simpa using hu⟩
    · have huI : u ∈ I := (hSI hu).resolve_left huB
      cases q with
      | nil => exact (hz huI).elim
      | cons huw tail =>
          have hwS := hstep huI huw
          rcases cut tail hwS with ⟨b, hb, r, hr⟩
          refine ⟨b, hb, r.cons huw, ?_⟩
          intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hr x hx
  exact cut p hv

/-- Every cell meeting a bounded planar set reaches a cell meeting its spatial
frontier by a finite ambient walk all of whose cells still meet the set. -/
theorem exists_walk_to_spatial_boundary
    {V : Type*} [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (Q : Set Plane) (hQ : Bornology.IsBounded Q) (v : V) (hv : Hits F Q v) :
    ∃ a : V, Hits F (frontier Q) a ∧
      ∃ p : F.graph.toSimpleGraph.Walk v a,
        ∀ x ∈ p.support, Hits F Q x := by
  obtain ⟨hcellConnected, -, -, -, -, hgraphConnected, -, hadjIntersects⟩ := id hF
  apply connected_exists_walk_to_boundary_within hgraphConnected
      (S := {w | Hits F Q w})
      (B := {w | Hits F (frontier Q) w})
      (I := {w | (F.cell w : Set Plane) ⊆ interior Q})
  · intro w hwQ
    by_cases hwBoundary : Hits F (frontier Q) w
    · exact Or.inl hwBoundary
    · apply Or.inr
      apply connected_subset_interior_of_inter_nonempty_of_disjoint_frontier
          (hcellConnected w) hwQ
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hwBoundary
  · intro w u hwInterior hwu
    rcases hadjIntersects hwu with ⟨x, hxw, hxu⟩
    exact ⟨x, hxu, interior_subset (hwInterior hxw)⟩
  · -- a cell meeting the complement of a ball containing `Q`: the uncovered set is
    -- `H¹`-null, hence has dense complement, so it meets that nonempty open set
    obtain ⟨r, hr⟩ := hQ.subset_closedBall (0 : Plane)
    have hballne : Metric.closedBall (0 : Plane) r ≠ (Set.univ : Set Plane) := by
      intro huniv
      apply NormedSpace.unbounded_univ ℝ Plane
      rw [← huniv]
      exact Metric.isBounded_closedBall
    rcases (Set.ne_univ_iff_exists_notMem _).mp hballne with ⟨x₀, hx₀⟩
    obtain ⟨x, hxout, w, hxw⟩ :=
      exists_mem_cell_of_isOpen hF (U := (Metric.closedBall (0 : Plane) r)ᶜ)
        Metric.isClosed_closedBall.isOpen_compl ⟨x₀, hx₀⟩
    refine ⟨w, ?_⟩
    intro hwInterior
    exact hxout (hr (interior_subset (hwInterior hxw)))
  · exact hv

/-- The preceding ambient walk lifts to the graph induced by the cells meeting
the bounded set. -/
theorem induced_reachable_spatial_boundary
    {V : Type*} [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (Q : Set Plane) (hQ : Bornology.IsBounded Q)
    (v : {w : V // Hits F Q w}) :
    ∃ a : {w : V // Hits F Q w},
      Hits F (frontier Q) a.1 ∧
        (F.graph.toSimpleGraph.induce {w | Hits F Q w}).Reachable v a := by
  rcases exists_walk_to_spatial_boundary F hF Q hQ v.1 v.2 with
    ⟨a, haBoundary, p, hp⟩
  have haQ : Hits F Q a := hp a p.end_mem_support
  refine ⟨⟨a, haQ⟩, haBoundary, ?_⟩
  exact ⟨by simpa using p.induce {w | Hits F Q w} hp⟩

/-- Boundary anchoring for a conductance restriction whose underlying simple
graph is the graph induced by cells meeting `Q`. -/
theorem boundaryAnchored_cells_hitting
    {V : Type*} [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (Q : Set Plane) (hQ : Bornology.IsBounded Q)
    (GQ : ReflectedWalk.ConductanceGraph {w : V // Hits F Q w})
    (hGQ : GQ.toSimpleGraph =
      F.graph.toSimpleGraph.induce {w | Hits F Q w}) :
    BoundaryAnchored GQ {a | Hits F (frontier Q) a.1} := by
  intro v
  rcases induced_reachable_spatial_boundary F hF Q hQ v with ⟨a, ha, hva⟩
  refine ⟨a, ha, ?_⟩
  rw [hGQ]
  exact hva

/-- The canonical conductance restriction to cells meeting a bounded set is
anchored at the cells meeting its spatial frontier. -/
theorem boundaryAnchored_restrictGraph_cells_hitting
    {V : Type*} [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (Q : Set Plane) (hQ : Bornology.IsBounded Q) :
    BoundaryAnchored (restrictGraph F.graph {w | Hits F Q w})
      {a | Hits F (frontier Q) a.1} := by
  exact boundaryAnchored_cells_hitting F hF Q hQ
    (restrictGraph F.graph {w | Hits F Q w})
    (restrictGraph_toSimpleGraph F.graph {w | Hits F Q w})

/-- If an edge crosses from the cells hitting `Q` to their complement, its
inside endpoint meets the spatial frontier of `Q`. -/
lemma hits_frontier_of_adj_of_hits_of_not_hits
    {V : Type*} [Countable V] (F : IndexedCells V) (hF : Geometry F)
    {Q : Set Plane} {v w : V}
    (hvw : F.graph.toSimpleGraph.Adj v w)
    (hvQ : Hits F Q v) (hwQ : ¬ Hits F Q w) :
    Hits F (frontier Q) v := by
  by_contra hvBoundary
  rcases hF with ⟨hcellConnected, _, _, _, _, _, _, hadjIntersects⟩
  have hvInterior : (F.cell v : Set Plane) ⊆ interior Q := by
    apply connected_subset_interior_of_inter_nonempty_of_disjoint_frontier
        (hcellConnected v) hvQ
    rw [Set.disjoint_iff_inter_eq_empty]
    exact Set.not_nonempty_iff_eq_empty.mp hvBoundary
  rcases hadjIntersects hvw with ⟨x, hxv, hxw⟩
  apply hwQ
  exact ⟨x, hxw, interior_subset (hvInterior hxv)⟩

end ReflectedGMS
