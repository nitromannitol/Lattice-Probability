/-
# Closing two finite polygonal crosscuts for ray parity

Consecutive edges of a vertex list have boundary equal, modulo two, to the
sum of its first and last vertices. Appending the edge lists of two chains
with the same endpoints cancels this boundary. Their segment trace is exactly
the union of the original chain traces when the endpoints differ. Geometric
simplicity supplies nondegeneracy of every consecutive edge.
-/
import LatticeProb.Topology.PolygonalParityCoordinates
import LatticeProb.Topology.SimplePolygonalChain



open Set
namespace LatticeProb.Topology.PolygonalParity

/-- The consecutive edges of a finite vertex list, without an added closing edge. -/
def chainEdges {α : Type*} : List α → List (α × α)
  | a :: b :: rest => (a, b) :: chainEdges (b :: rest)
  | _ => []

/-- Consecutive edge boundary markers telescope to the two endpoint markers,
with coefficients in `ZMod 2`. A singleton contributes twice the same marker. -/
theorem sum_chainEdges_boundary {α : Type*} (f : α → ZMod 2) :
    ∀ (vs : List α) (hv : vs ≠ []),
      ((chainEdges vs).map (fun P => f P.1 + f P.2)).sum =
        f (vs.head hv) + f (vs.getLast hv)
  | [], hv => (hv rfl).elim
  | [a], _ => (add_self_zmod_two (f a)).symm
  | a :: b :: rest, hv => by
    change f a + f b + ((chainEdges (b :: rest)).map (fun P => f P.1 + f P.2)).sum = _
    rw [sum_chainEdges_boundary f (b :: rest) (List.cons_ne_nil _ _),
      List.getLast_cons (List.cons_ne_nil b rest)]
    change f a + f b + (f b + f ((b :: rest).getLast _)) =
      f a + f ((b :: rest).getLast _)
    rw [← add_assoc, add_assoc (f a) (f b) (f b), add_self_zmod_two, add_zero]

/-- The exact coordinate trace of a chain with at least one edge agrees with
its vertex-list polygonal trace. -/
theorem coordinateEdgeTrace_chainEdges_cons_cons (a b : ℝ × ℝ)
    (rest : List (ℝ × ℝ)) :
    coordinateEdgeTrace (chainEdges (a :: b :: rest)) = polygonalChain (a :: b :: rest) := by
  induction rest generalizing a b with
  | nil =>
    change coordinateEdgeTrace [(a, b)] = segment ℝ a b ∪ {b}
    have htrace : coordinateEdgeTrace [(a, b)] = segment ℝ a b := by
      ext z
      simp only [coordinateEdgeTrace, mem_iUnion, exists_prop, List.mem_singleton,
        exists_eq_left]
    rw [htrace, union_eq_left.mpr (singleton_subset_iff.mpr (right_mem_segment ℝ a b))]
  | cons c rest ih =>
    have htrace : coordinateEdgeTrace ((a, b) :: chainEdges (b :: c :: rest)) =
        segment ℝ a b ∪ coordinateEdgeTrace (chainEdges (b :: c :: rest)) := by
      ext z
      simp only [coordinateEdgeTrace, mem_iUnion, exists_prop, List.mem_cons, mem_union]
      aesop
    rw [chainEdges, htrace, ih]
    rfl

/-- Distinct first and last vertices exclude a singleton, so the edge trace
is the full polygonal chain trace. -/
theorem coordinateEdgeTrace_chainEdges {vs : List (ℝ × ℝ)} (hv : vs ≠ [])
    (hne : vs.head hv ≠ vs.getLast hv) :
    coordinateEdgeTrace (chainEdges vs) = polygonalChain vs := by
  cases vs with
  | nil => exact (hv rfl).elim
  | cons a rest =>
    cases rest with
    | nil => exact (hne rfl).elim
    | cons b rest => exact coordinateEdgeTrace_chainEdges_cons_cons a b rest

/-- Geometric simplicity supplies distinct endpoints for each consecutive edge. -/
theorem nondeg_chainEdges_of_simple {vs : List (ℝ × ℝ)} (hs : IsSimplePolygonalChain vs) :
    ∀ P ∈ chainEdges vs, P.1 ≠ P.2 := by
  induction vs with
  | nil => exact hs.elim
  | cons a rest ih =>
    cases rest with
    | nil => simp only [chainEdges, List.not_mem_nil, false_implies, implies_true]
    | cons b rest =>
      intro P hP
      rcases List.mem_cons.mp hP with rfl | hP
      · exact hs.1
      · exact ih hs.2.1 P hP

/-- Two coordinate edge traces concatenate by exact set union. -/
theorem coordinateEdgeTrace_append (L₁ L₂ : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    coordinateEdgeTrace (L₁ ++ L₂) = coordinateEdgeTrace L₁ ∪ coordinateEdgeTrace L₂ := by
  ext z
  simp only [coordinateEdgeTrace, mem_iUnion, exists_prop, List.mem_append, mem_union]
  aesop

/-- **Closed crosscut edge chain.** The two actual consecutive edge lists
with matching endpoints form a closed chain after the coordinate map. No
cyclicity or endpoint-cancellation conclusion is assumed. -/
theorem isClosedChain_coordinateEdges_append {vs us : List (ℝ × ℝ)}
    (hv : vs ≠ []) (hu : us ≠ [])
    (hhead : vs.head hv = us.head hu) (hlast : vs.getLast hv = us.getLast hu) :
    IsClosedChain (coordinateEdges (chainEdges vs ++ chainEdges us)) := by
  intro f
  change (((chainEdges vs ++ chainEdges us).map
    (fun P => (coordinateEquiv P.1, coordinateEquiv P.2))).map
    (fun P => f P.1 + f P.2)).sum = 0
  rw [List.map_map]
  change ((chainEdges vs ++ chainEdges us).map
    (fun P => (f ∘ coordinateEquiv) P.1 + (f ∘ coordinateEquiv) P.2)).sum = 0
  rw [List.map_append, List.sum_append, sum_chainEdges_boundary _ vs hv,
    sum_chainEdges_boundary _ us hu, hhead, hlast]
  exact add_self_zmod_two _

/-- Two simple coordinate chains produce nondegenerate Euclidean edges. -/
theorem nondeg_coordinateEdges_append {vs us : List (ℝ × ℝ)}
    (hvs : IsSimplePolygonalChain vs) (hus : IsSimplePolygonalChain us) :
    ∀ P ∈ coordinateEdges (chainEdges vs ++ chainEdges us), P.Nondeg := by
  intro P hP
  obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hP
  intro heq
  have hQne : Q.1 ≠ Q.2 := by
    rcases List.mem_append.mp hQ with hQ | hQ
    · exact nondeg_chainEdges_of_simple hvs Q hQ
    · exact nondeg_chainEdges_of_simple hus Q hQ
  exact hQne (coordinateEquiv.injective heq)

end LatticeProb.Topology.PolygonalParity
