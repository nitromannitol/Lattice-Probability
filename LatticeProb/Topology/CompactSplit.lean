import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Connected.Clopen

/-!
# Splitting a compact set between two closed sets

Let `S` be a compact subset of a Hausdorff space and `E`, `G` closed sets such that no preconnected subset of `S`
meets both `E` and `G`. Then `S` is the disjoint union of two compact sets `S_E` and `S_G` with `S_E` missing `G`
and `S_G` missing `E`.

The proof works in the compact Hausdorff subspace `S`. There the connected component of a point equals the
intersection of its clopen neighbourhoods (`connectedComponent_eq_iInter_isClopen`). The component of a point of `E`
misses `G`, so by compactness of `G ∩ S` some clopen neighbourhood of the point misses `G`. Finitely many of these
cover the compact set `E ∩ S`; their union is `S_E` and its complement in `S` is `S_G`.

* `exists_isClopen_subset_compl_of_connectedComponent_subset`: in a compact Hausdorff space, a closed set missing the
  connected component of a point misses some clopen neighbourhood of that point.
* `exists_compact_split`: the splitting statement.
-/

open Set

namespace LatticeProb.Topology

/-- In a compact Hausdorff space, if the connected component of `x` misses a closed set `G`, then some clopen
neighbourhood of `x` misses `G`. -/
theorem exists_isClopen_subset_compl_of_connectedComponent_subset {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] {x : X} {G : Set X} (hG : IsClosed G)
    (hx : Disjoint (connectedComponent x) G) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ Disjoint V G := by
  rw [connectedComponent_eq_iInter_isClopen] at hx
  obtain ⟨I, hI⟩ := hG.isCompact.elim_finite_subfamily_closed
    (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => (s : Set X)) (fun s => s.2.1.isClosed)
    hx.symm
  refine ⟨⋂ s ∈ I, (s : Set X), ?_, ?_, ?_⟩
  · exact isClopen_biInter_finset fun s _ => s.2.1
  · exact mem_iInter₂.2 fun s _ => s.2.2
  · exact hI.symm

/-- **Compact two-piece split.** Let `S` be compact in a Hausdorff space and `E`, `G` closed. If no preconnected
subset of `S` meets both `E` and `G`, then `S = S_E ∪ S_G` with `S_E`, `S_G` disjoint and compact, `S_E` missing `G`
and `S_G` missing `E`. -/
theorem exists_compact_split {X : Type*} [TopologicalSpace X] [T2Space X] {S E G : Set X}
    (hS : IsCompact S) (hE : IsClosed E) (hG : IsClosed G)
    (h : ∀ T ⊆ S, IsPreconnected T → ¬ ((T ∩ E).Nonempty ∧ (T ∩ G).Nonempty)) :
    ∃ SE SG : Set X, IsCompact SE ∧ IsCompact SG ∧ Disjoint SE SG ∧ SE ∪ SG = S ∧
      Disjoint SE G ∧ Disjoint SG E := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  set E' : Set S := (↑) ⁻¹' E with hE'
  set G' : Set S := (↑) ⁻¹' G with hG'
  have hE'c : IsClosed E' := hE.preimage continuous_subtype_val
  have hG'c : IsClosed G' := hG.preimage continuous_subtype_val
  -- every point of `E'` has a clopen neighbourhood missing `G'`
  have hloc : ∀ p : S, p ∈ E' → ∃ V : Set S, IsClopen V ∧ p ∈ V ∧ Disjoint V G' := by
    intro p hp
    refine exists_isClopen_subset_compl_of_connectedComponent_subset hG'c ?_
    rw [Set.disjoint_left]
    intro q hq hqG
    have hT : IsPreconnected (((↑) : S → X) '' connectedComponent p) :=
      isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
    refine h _ (by rintro _ ⟨r, -, rfl⟩; exact r.2) hT ⟨⟨p, ⟨p, mem_connectedComponent, rfl⟩, hp⟩, ?_⟩
    exact ⟨q, ⟨q, hq, rfl⟩, hqG⟩
  choose! V hV using hloc
  obtain ⟨I, hI⟩ := hE'c.isCompact.elim_finite_subcover (fun p : E' => V p)
    (fun p => (hV p p.2).1.isOpen) (fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, (hV p hp).2.1⟩)
  set W : Set S := ⋃ p ∈ I, V (p : S) with hW
  have hWc : IsClopen W := I.finite_toSet.isClopen_biUnion fun p _ => (hV p p.2).1
  have hWG : Disjoint W G' := by
    rw [Set.disjoint_left]
    intro q hq hqG
    obtain ⟨p, -, hqp⟩ := mem_iUnion₂.1 hq
    exact Set.disjoint_left.1 (hV p p.2).2.2 hqp hqG
  refine ⟨((↑) : S → X) '' W, ((↑) : S → X) '' Wᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hWc.isClosed.isCompact.image continuous_subtype_val
  · exact hWc.compl.isClosed.isCompact.image continuous_subtype_val
  · rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ ⟨r', hr', hrr'⟩
    rw [Subtype.val_injective hrr'] at hr'
    exact hr' hr
  · rw [← image_union, union_compl_self, image_univ, Subtype.range_coe]
  · rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrG
    exact Set.disjoint_left.1 hWG hr hrG
  · rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrE
    exact hr (hI hrE)

end LatticeProb.Topology
