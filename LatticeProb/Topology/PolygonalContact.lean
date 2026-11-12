/-
# First and last contacts of a finite polygonal chain with a closed set

A finite polygonal chain that meets a closed set `A` has a final piece, ending at the last vertex of the chain,
that meets `A` only at its initial point, and an initial piece, starting at the first vertex, that meets `A`
only at its final point. Both pieces are again finite polygonal chains inside the original trace.
-/
import LatticeProb.Topology.PolygonalLastContact

open Set

namespace LatticeProb.Topology

/-- **Last contact of a chain.** If a finite polygonal chain meets a closed set `A`, a final piece of it,
ending at the last vertex, meets `A` exactly at its initial point. -/
theorem exists_suffix_inter_eq_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set E} (hA : IsClosed A) {vs : List E} (hv : vs ≠ [])
    (hmeet : (polygonalChain vs ∩ A).Nonempty) :
    ∃ q ∈ A, ∃ ws : List E, ∃ hw : ws ≠ [], ws.head hw = q ∧ ws.getLast hw = vs.getLast hv ∧
      polygonalChain ws ⊆ polygonalChain vs ∧ polygonalChain ws ∩ A = {q} := by
  induction vs with
  | nil => exact absurd rfl hv
  | cons x tl ih =>
    cases tl with
    | nil =>
      obtain ⟨p, hp, hpA⟩ := hmeet
      rw [polygonal_chain_singleton, mem_singleton_iff] at hp
      subst hp
      refine ⟨p, hpA, [p], List.cons_ne_nil _ _, rfl, rfl, subset_rfl, ?_⟩
      rw [polygonal_chain_singleton, inter_eq_left.2 (singleton_subset_iff.2 hpA)]
    | cons y rest =>
      have hsplit : polygonalChain (x :: y :: rest) = segment ℝ x y ∪ polygonalChain (y :: rest) := rfl
      have hlast : (x :: y :: rest).getLast hv = (y :: rest).getLast (List.cons_ne_nil _ _) :=
        List.getLast_cons _
      by_cases htl : (polygonalChain (y :: rest) ∩ A).Nonempty
      · obtain ⟨q, hqA, ws, hw, hhead, hwl, hsub, hint⟩ := ih (List.cons_ne_nil _ _) htl
        refine ⟨q, hqA, ws, hw, hhead, hwl.trans hlast.symm, ?_, hint⟩
        rw [hsplit]
        exact hsub.trans subset_union_right
      · rw [not_nonempty_iff_eq_empty] at htl
        have hyA : y ∉ A := fun hy =>
          (eq_empty_iff_forall_notMem.1 htl) y ⟨mem_polygonal_chain_of_mem (List.mem_cons_self ..), hy⟩
        have hseg : (segment ℝ x y ∩ A).Nonempty := by
          obtain ⟨p, hp, hpA⟩ := hmeet
          rw [hsplit] at hp
          rcases hp with hp | hp
          · exact ⟨p, hp, hpA⟩
          · have hpt : p ∈ polygonalChain (y :: rest) ∩ A := ⟨hp, hpA⟩
            rw [htl] at hpt
            exact absurd hpt (notMem_empty p)
        obtain ⟨p, hpseg, hpA⟩ := hseg
        have hS : IsCompact (A ∩ segment ℝ x y) := (isCompact_segment x y).inter_left hA
        obtain ⟨q, ⟨hqA, hqxy⟩, -, -, hqsub, hqint, -⟩ :=
          exists_last_contact_segment hS (a := p) (b := y) ⟨hpA, hpseg⟩ (fun h => hyA h.1)
        have hqy : segment ℝ q y ⊆ segment ℝ x y :=
          (convex_segment x y).segment_subset hqxy (right_mem_segment ℝ x y)
        refine ⟨q, hqA, q :: y :: rest, List.cons_ne_nil _ _, rfl, ?_, ?_, ?_⟩
        · rw [hlast]
          exact List.getLast_cons _
        · change segment ℝ q y ∪ polygonalChain (y :: rest) ⊆ polygonalChain (x :: y :: rest)
          rw [hsplit]
          exact union_subset_union_left _ hqy
        · change (segment ℝ q y ∪ polygonalChain (y :: rest)) ∩ A = {q}
          rw [union_inter_distrib_right, htl, union_empty, ← hqint]
          ext z
          constructor
          · rintro ⟨hz, hzA⟩
            exact ⟨hz, hzA, hqy hz⟩
          · rintro ⟨hz, hzA, -⟩
            exact ⟨hz, hzA⟩

/-- **First contact of a chain.** If a finite polygonal chain meets a closed set `A`, an initial piece of it,
starting at the first vertex, meets `A` exactly at its final point. -/
theorem exists_prefix_inter_eq_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set E} (hA : IsClosed A) {vs : List E} (hv : vs ≠ [])
    (hmeet : (polygonalChain vs ∩ A).Nonempty) :
    ∃ q ∈ A, ∃ ws : List E, ∃ hw : ws ≠ [], ws.head hw = vs.head hv ∧ ws.getLast hw = q ∧
      polygonalChain ws ⊆ polygonalChain vs ∧ polygonalChain ws ∩ A = {q} := by
  induction vs with
  | nil => exact absurd rfl hv
  | cons x tl ih =>
    by_cases hxA : x ∈ A
    · refine ⟨x, hxA, [x], List.cons_ne_nil _ _, rfl, rfl, ?_, ?_⟩
      · rw [polygonal_chain_singleton, singleton_subset_iff]
        exact mem_polygonal_chain_of_mem (List.mem_cons_self ..)
      · rw [polygonal_chain_singleton, inter_eq_left.2 (singleton_subset_iff.2 hxA)]
    cases tl with
    | nil =>
      obtain ⟨p, hp, hpA⟩ := hmeet
      rw [polygonal_chain_singleton, mem_singleton_iff] at hp
      exact absurd (hp ▸ hpA) hxA
    | cons y rest =>
      have hsplit : polygonalChain (x :: y :: rest) = segment ℝ x y ∪ polygonalChain (y :: rest) := rfl
      by_cases hseg : (segment ℝ x y ∩ A).Nonempty
      · obtain ⟨p, hpseg, hpA⟩ := hseg
        have hS : IsCompact (A ∩ segment ℝ x y) := (isCompact_segment x y).inter_left hA
        obtain ⟨q, ⟨hqA, hqxy⟩, -, -, -, hqint, -⟩ :=
          exists_last_contact_segment hS (a := p) (b := x) ⟨hpA, hpseg⟩ (fun h => hxA h.1)
        have hqx : segment ℝ x q ⊆ segment ℝ x y :=
          (convex_segment x y).segment_subset (left_mem_segment ℝ x y) hqxy
        refine ⟨q, hqA, [x, q], List.cons_ne_nil _ _, rfl, rfl, ?_, ?_⟩
        · change segment ℝ x q ∪ {q} ⊆ polygonalChain (x :: y :: rest)
          rw [hsplit]
          exact union_subset (hqx.trans subset_union_left)
            (singleton_subset_iff.2 (Or.inl hqxy))
        · change (segment ℝ x q ∪ {q}) ∩ A = {q}
          apply subset_antisymm
          · rintro z ⟨hz | hz, hzA⟩
            · have hz' : z ∈ segment ℝ q x ∩ (A ∩ segment ℝ x y) :=
                ⟨by rw [segment_symm]; exact hz, hzA, hqx hz⟩
              rw [hqint] at hz'
              exact hz'
            · exact hz
          · rintro z hz
            rw [mem_singleton_iff] at hz
            subst hz
            exact ⟨Or.inr rfl, hqA⟩
      · have htl : (polygonalChain (y :: rest) ∩ A).Nonempty := by
          obtain ⟨p, hp, hpA⟩ := hmeet
          rw [hsplit] at hp
          rcases hp with hp | hp
          · exact absurd ⟨p, hp, hpA⟩ hseg
          · exact ⟨p, hp, hpA⟩
        obtain ⟨q, hqA, ws, hw, hhead, hwl, hsub, hint⟩ := ih (List.cons_ne_nil _ _) htl
        obtain ⟨z, t, rfl⟩ := List.exists_cons_of_ne_nil hw
        have hz : z = y := hhead
        subst hz
        refine ⟨q, hqA, x :: z :: t, List.cons_ne_nil _ _, rfl, ?_, ?_, ?_⟩
        · rw [List.getLast_cons (List.cons_ne_nil _ _)]
          exact hwl
        · change segment ℝ x z ∪ polygonalChain (z :: t) ⊆ polygonalChain (x :: z :: rest)
          rw [hsplit]
          exact union_subset_union_right _ hsub
        · change (segment ℝ x z ∪ polygonalChain (z :: t)) ∩ A = {q}
          rw [union_inter_distrib_right, hint, not_nonempty_iff_eq_empty.1 hseg, empty_union]

end LatticeProb.Topology
