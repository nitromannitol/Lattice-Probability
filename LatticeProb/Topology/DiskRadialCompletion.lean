/-
# Outside completions retaining a radial first edge

Prune only the middle polygonal connection in the open exterior, then attach
the two original outward radial segments. This retains a literal doubled first
vertex, nondegenerate edges, and a remaining trace disjoint from the first
circle endpoint. The whole completion need not be simple for crossing parity.
-/
import LatticeProb.Topology.DiskEndpointGeometry



open Set
namespace LatticeProb.Topology
open PolygonalParity

/-- Appending one vertex adds exactly the last consecutive edge. -/
theorem chainEdges_concat {α : Type*} : ∀ (vs : List α) (hv : vs ≠ []) (b : α),
    chainEdges (vs ++ [b]) = chainEdges vs ++ [(vs.getLast hv, b)]
  | [], hv, _ => (hv rfl).elim
  | [a], _, _ => rfl
  | a :: c :: rest, _, b => by
    change (a, c) :: chainEdges ((c :: rest) ++ [b]) = _
    rw [chainEdges_concat (c :: rest) (List.cons_ne_nil _ _) b,
      List.getLast_cons (List.cons_ne_nil c rest)]
    rfl

/-- Consecutive edge trace is contained in the actual vertex-list trace,
including empty and singleton lists. -/
theorem coordinateEdgeTrace_chainEdges_subset (vs : List (ℝ × ℝ)) :
    coordinateEdgeTrace (chainEdges vs) ⊆ polygonalChain vs := by
  cases vs with
  | nil => simp only [chainEdges, coordinateEdgeTrace, List.not_mem_nil, iUnion_false,
      iUnion_empty, empty_subset]
  | cons a rest =>
    cases rest with
    | nil => simp only [chainEdges, coordinateEdgeTrace, List.not_mem_nil, iUnion_false,
        iUnion_empty, empty_subset]
    | cons b rest => exact le_of_eq (coordinateEdgeTrace_chainEdges_cons_cons a b rest)

/-- A unit-circle point differs from its doubled point. -/
theorem circle_point_ne_double {a : ℝ × ℝ} (ha : a.1 ^ 2 + a.2 ^ 2 = 1) :
    a ≠ (2 : ℝ) • a := by
  intro heq
  have h := coordinateRadial_smul_pos ha (by norm_num : (1 : ℝ) < 2)
  rw [← heq, coordinateRadial] at h
  simp only [sub_self, mul_zero, add_zero] at h
  exact lt_irrefl 0 h

/-- **Radial outside completion.** Distinct original circle endpoints have
a finite outside completion whose first vertex after the endpoint is its
literal double. Every edge is nondegenerate and the remaining trace avoids
that endpoint. Pruning is applied only to the middle exterior connection. -/
theorem exists_radial_polygonal_outside_completion (θ φ : ℝ)
    (hne : ((Real.cos θ, Real.sin θ) : ℝ × ℝ) ≠ (Real.cos φ, Real.sin φ)) :
    ∃ tail : List (ℝ × ℝ),
      let ws := (Real.cos θ, Real.sin θ) :: (2 : ℝ) • (Real.cos θ, Real.sin θ) :: tail
      ws.getLast (List.cons_ne_nil _ _) = (Real.cos φ, Real.sin φ) ∧
      polygonalChain ws \ {(Real.cos θ, Real.sin θ), (Real.cos φ, Real.sin φ)} ⊆
        {z | 1 < z.1 ^ 2 + z.2 ^ 2} ∧
      (Real.cos θ, Real.sin θ) ∉
        polygonalChain ((2 : ℝ) • (Real.cos θ, Real.sin θ) :: tail) ∧
      (∀ P ∈ chainEdges ws, P.1 ≠ P.2) := by
  let a : ℝ × ℝ := (Real.cos θ, Real.sin θ)
  let b : ℝ × ℝ := (Real.cos φ, Real.sin φ)
  obtain ⟨vs, hv, hhead, hlast, hsub⟩ := exists_polygonal_chain_outside_coordinate_disk θ φ
  obtain ⟨us, hu, hs, uh, ul, htrace⟩ := exists_simple_polygonal_chain vs hv
  have uhead : us.head hu = (2 : ℝ) • a := uh.trans hhead
  have ulast : us.getLast hu = (2 : ℝ) • b := ul.trans hlast
  have uout : polygonalChain us ⊆ {z | 1 < z.1 ^ 2 + z.2 ^ 2} := htrace.trans hsub
  have ha : a.1 ^ 2 + a.2 ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hb : b.1 ^ 2 + b.2 ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
  have hat : a ∉ polygonalChain (us ++ [b]) := by
    rw [polygonal_chain_concat hu, ulast]
    rintro (h | h)
    · have hgt := uout h
      change 1 < a.1 ^ 2 + a.2 ^ 2 at hgt
      rw [ha] at hgt
      exact lt_irrefl 1 hgt
    · rw [segment_symm] at h
      have hgt := one_lt_coordinate_square_of_mem_outward_segment hb h hne
      rw [ha] at hgt
      exact lt_irrefl 1 hgt
  have hout : polygonalChain ((a :: us) ++ [b]) \ {a, b} ⊆
      {z | 1 < z.1 ^ 2 + z.2 ^ 2} := by
    rw [polygonal_chain_add_endpoints a b hu, uhead, ulast]
    rintro z ⟨(hz | hz) | hz, hznot⟩
    · exact one_lt_coordinate_square_of_mem_outward_segment ha hz
        (fun heq => hznot (heq ▸ mem_insert a {b}))
    · exact uout hz
    · rw [segment_symm] at hz
      exact one_lt_coordinate_square_of_mem_outward_segment hb hz
        (fun heq => hznot (by rw [heq]; exact mem_insert_of_mem a (mem_singleton b)))
  have hnd : ∀ P ∈ chainEdges ((a :: us) ++ [b]), P.1 ≠ P.2 := by
    rw [chainEdges_concat (a :: us) (List.cons_ne_nil _ _) b,
      List.getLast_cons hu, ulast]
    cases us with
    | nil => exact (hu rfl).elim
    | cons c rest =>
      change c = (2 : ℝ) • a at uhead
      subst c
      intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · change P ∈ (a, (2 : ℝ) • a) :: chainEdges ((2 : ℝ) • a :: rest) at hP
        rcases List.mem_cons.mp hP with rfl | hP
        · exact circle_point_ne_double ha
        · exact nondeg_chainEdges_of_simple hs P hP
      · have heq := List.mem_singleton.mp hP
        rw [heq]
        exact (circle_point_ne_double hb).symm
  cases us with
  | nil => exact (hu rfl).elim
  | cons c rest =>
    change c = (2 : ℝ) • a at uhead
    subst c
    refine ⟨rest ++ [b], ?_, hout, hat, hnd⟩
    change ((a :: (2 : ℝ) • a :: rest) ++ [b]).getLast _ = b
    exact List.getLast_append_singleton _

end LatticeProb.Topology
