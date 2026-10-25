module

/-
# Geometrically simple finite polygonal chains

A chain is simple when each nondegenerate first segment meets the remaining
trace only at its next vertex. Prefix cutting preserves this property. Finite
induction and the last-contact splice erase intersections and overlaps without
enlarging the original trace.
-/
public import LatticeProb.Topology.PolygonalLastContact
public import Mathlib.Data.List.Induction

@[expose] public section



open Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite chain is geometrically simple if each edge is nondegenerate and
meets its remaining trace exactly at its next vertex. Singletons are allowed;
the empty list is excluded. This predicate describes actual segment traces. -/
def IsSimplePolygonalChain : List E → Prop
  | [] => False
  | [_] => True
  | a :: b :: rest => a ≠ b ∧ IsSimplePolygonalChain (b :: rest) ∧
      segment ℝ a b ∩ polygonalChain (b :: rest) = {b}

/-- A geometrically simple chain is nonempty. -/
theorem IsSimplePolygonalChain.ne_nil {vs : List E} (h : IsSimplePolygonalChain vs) :
    vs ≠ [] := by
  rintro rfl
  exact h

/-- Every point of a simple chain is the last point of a simple prefix,
obtained by cutting an original segment and keeping its earlier vertices. -/
theorem IsSimplePolygonalChain.exists_prefix : ∀ {vs : List E}
    (hs : IsSimplePolygonalChain vs) {q : E}, q ∈ polygonalChain vs →
    ∃ us : List E, ∃ hu : us ≠ [], IsSimplePolygonalChain us ∧
      us.head hu = vs.head hs.ne_nil ∧ us.getLast hu = q ∧
      polygonalChain us ⊆ polygonalChain vs
  | [], hs, _, _ => hs.elim
  | [v], _, q, hq => by
    have hEq : q = v := mem_singleton_iff.mp hq
    exact ⟨[v], List.cons_ne_nil _ _, trivial, rfl, hEq.symm, subset_rfl⟩
  | a :: b :: rest, hs, q, hq => by
    rcases hq with hfirst | htail
    · by_cases hqa : q = a
      · subst q
        exact ⟨[a], List.cons_ne_nil _ _, trivial, rfl, rfl,
          singleton_subset_iff.mpr (Or.inl (left_mem_segment ℝ a b))⟩
      · have hseg : segment ℝ a q ⊆ segment ℝ a b :=
          (convex_segment a b).segment_subset (left_mem_segment ℝ a b) hfirst
        refine ⟨[a, q], List.cons_ne_nil _ _, ?_, rfl, rfl, ?_⟩
        · exact ⟨Ne.symm hqa, trivial,
            inter_eq_right.mpr (singleton_subset_iff.mpr (right_mem_segment ℝ a q))⟩
        · exact union_subset (hseg.trans subset_union_left)
            (singleton_subset_iff.mpr (Or.inl hfirst))
    · obtain ⟨us, hu, hus, hhead, hlast, hsub⟩ := hs.2.1.exists_prefix htail
      refine ⟨a :: us, List.cons_ne_nil _ _, ?_, rfl, ?_, ?_⟩
      · cases us with
        | nil => exact (hu rfl).elim
        | cons c cs =>
          change c = b at hhead
          subst c
          refine ⟨hs.1, hus, ?_⟩
          apply subset_antisymm
          · exact (inter_subset_inter_right _ hsub).trans (le_of_eq hs.2.2)
          · exact singleton_subset_iff.mpr
              ⟨right_mem_segment ℝ a b, head_mem_polygonal_chain hu⟩
      · rw [List.getLast_cons hu]
        exact hlast
      · cases us with
        | nil => exact (hu rfl).elim
        | cons c cs =>
          change c = b at hhead
          subst c
          exact union_subset_union subset_rfl hsub

/-- Appending a nondegenerate segment meeting the old trace only at its last
vertex preserves geometric simplicity. -/
theorem IsSimplePolygonalChain.concat : ∀ {vs : List E}
    (hs : IsSimplePolygonalChain vs) {z : E},
    vs.getLast hs.ne_nil ≠ z →
    segment ℝ (vs.getLast hs.ne_nil) z ∩ polygonalChain vs = {vs.getLast hs.ne_nil} →
    IsSimplePolygonalChain (vs ++ [z])
  | [], hs, _, _, _ => hs.elim
  | [v], _, z, hne, _ =>
      ⟨hne, trivial, inter_eq_right.mpr (singleton_subset_iff.mpr (right_mem_segment ℝ v z))⟩
  | a :: b :: rest, hs, z, hne, hmeet => by
    have hlast : (a :: b :: rest).getLast hs.ne_nil =
        (b :: rest).getLast hs.2.1.ne_nil := List.getLast_cons _
    have hlastmem : (b :: rest).getLast hs.2.1.ne_nil ∈ polygonalChain (b :: rest) :=
      getLast_mem_polygonal_chain _
    have hmeetTail : segment ℝ ((b :: rest).getLast hs.2.1.ne_nil) z ∩
        polygonalChain (b :: rest) = {(b :: rest).getLast hs.2.1.ne_nil} := by
      apply subset_antisymm
      · rw [← hlast]
        exact (inter_subset_inter_right _ subset_union_right).trans (le_of_eq hmeet)
      · exact singleton_subset_iff.mpr ⟨left_mem_segment ℝ _ z, hlastmem⟩
    have htail : IsSimplePolygonalChain ((b :: rest) ++ [z]) :=
      hs.2.1.concat (hlast ▸ hne) hmeetTail
    refine ⟨hs.1, htail, ?_⟩
    change segment ℝ a b ∩ polygonalChain ((b :: rest) ++ [z]) = {b}
    rw [polygonal_chain_concat hs.2.1.ne_nil]
    apply subset_antisymm
    · rintro w ⟨hwseg, hwold | hwnew⟩
      · exact le_of_eq hs.2.2 ⟨hwseg, hwold⟩
      · have hwlast : w = (b :: rest).getLast hs.2.1.ne_nil := by
          rw [← hlast] at hwnew ⊢
          exact mem_singleton_iff.mp (le_of_eq hmeet ⟨hwnew, Or.inl hwseg⟩)
        exact le_of_eq hs.2.2 ⟨hwseg, hwlast ▸ hlastmem⟩
    · exact singleton_subset_iff.mpr
        ⟨right_mem_segment ℝ a b, Or.inl (head_mem_polygonal_chain hs.2.1.ne_nil)⟩

/-- **Finite geometric loop pruning.** Every nonempty finite polygonal chain
has a geometrically simple chain with the same endpoints and trace contained
in its original trace. The last-contact step also handles collinear overlaps. -/
theorem exists_simple_polygonal_chain (vs : List E) (hv : vs ≠ []) :
    ∃ us : List E, ∃ hu : us ≠ [], IsSimplePolygonalChain us ∧
      us.head hu = vs.head hv ∧ us.getLast hu = vs.getLast hv ∧
      polygonalChain us ⊆ polygonalChain vs := by
  classical
  induction vs using List.reverseRecOn with
  | nil => exact (hv rfl).elim
  | append_singleton vs b ih =>
    by_cases hvs : vs = []
    · subst vs
      exact ⟨[b], List.cons_ne_nil _ _, trivial, rfl, rfl, subset_rfl⟩
    · obtain ⟨us, hu, hus, hhead, hlast, hsub⟩ := ih hvs
      by_cases hb : b ∈ polygonalChain us
      · obtain ⟨ws, hw, hws, hwhead, hwlast, hwsub⟩ := hus.exists_prefix hb
        refine ⟨ws, hw, hws, ?_, ?_, ?_⟩
        · rw [List.head_append_of_ne_nil hvs]
          exact hwhead.trans hhead
        · rw [List.getLast_append_singleton]
          exact hwlast
        · rw [polygonal_chain_concat hvs]
          exact (hwsub.trans hsub).trans subset_union_left
      · obtain ⟨q, hq, _, hqb, hseg, hmeet, _⟩ :=
          exists_last_contact_segment (isCompact_polygonal_chain us)
            (getLast_mem_polygonal_chain hu) hb
        obtain ⟨ws, hw, hws, hwhead, hwlast, hwsub⟩ := hus.exists_prefix hq
        have hmeetws : segment ℝ q b ∩ polygonalChain ws = {q} := by
          apply subset_antisymm
          · exact (inter_subset_inter_right _ hwsub).trans (le_of_eq hmeet)
          · exact singleton_subset_iff.mpr
              ⟨left_mem_segment ℝ q b, hwlast ▸ getLast_mem_polygonal_chain hw⟩
        refine ⟨ws ++ [b], List.append_ne_nil_of_left_ne_nil hw [b],
          hws.concat (hwlast ▸ hqb) (hwlast ▸ hmeetws), ?_, ?_, ?_⟩
        · rw [List.head_append_of_ne_nil hw, List.head_append_of_ne_nil hvs]
          exact hwhead.trans hhead
        · simp only [List.getLast_append_singleton]
        · rw [polygonal_chain_concat hw, hwlast, polygonal_chain_concat hvs]
          exact union_subset_union (hwsub.trans hsub) (hlast ▸ hseg)

end LatticeProb.Topology
