/-
# Last contacts and finite polygonal splicing

Compactness gives the last contact of a segment with a finite chain. The
remaining closed segment meets the old trace at just that contact, including
when earlier segments overlap it along a line. A finite prefix ending at the
contact supplies a new polygonal chain with the same initial point.
-/
import LatticeProb.Topology.PolygonalChain
import Mathlib.Topology.Order.Compact



open Set AffineMap

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Last contact.** If a segment starts in a compact set and ends outside it,
there is a final contact `q`. The segment from `q` to the new endpoint meets
the entire compact set exactly at `q` and has an injective segment path.
No restriction on earlier intersections or collinear overlaps is required. -/
theorem exists_last_contact_segment {S : Set E} (hS : IsCompact S)
    {a b : E} (ha : a ∈ S) (hb : b ∉ S) :
    ∃ q ∈ S, q ∈ segment ℝ a b ∧ q ≠ b ∧
      segment ℝ q b ⊆ segment ℝ a b ∧
      segment ℝ q b ∩ S = {q} ∧ Function.Injective (Path.segment q b) := by
  let T : Set ℝ := Icc 0 1 ∩ (lineMap a b) ⁻¹' S
  have hf : Continuous (lineMap a b : ℝ → E) := by
    dsimp [lineMap]
    fun_prop
  have hT : IsCompact T := isCompact_Icc.inter_right (hS.isClosed.preimage hf)
  have hzero : (0 : ℝ) ∈ T := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    change lineMap a b 0 ∈ S
    rw [lineMap_apply_zero]
    exact ha
  obtain ⟨t, ht, hmax⟩ := hT.exists_isGreatest ⟨0, hzero⟩
  let q := lineMap a b t
  have hq : q ∈ S := ht.2
  have hqseg : q ∈ segment ℝ a b := lineMap_mem_segment ℝ a b ht.1
  have hqb : q ≠ b := fun h => hb (h ▸ hq)
  have him : lineMap a b '' Icc t 1 = segment ℝ q b := by
    rw [← segment_eq_Icc ht.1.2, image_segment, lineMap_apply_one]
  have hsub : segment ℝ q b ⊆ segment ℝ a b :=
    (convex_segment a b).segment_subset hqseg (right_mem_segment ℝ a b)
  refine ⟨q, hq, hqseg, hqb, hsub, ?_, Path.segment_injective_of_ne hqb⟩
  apply subset_antisymm
  · rintro w ⟨hwseg, hwS⟩
    rw [← him] at hwseg
    obtain ⟨s, hs, rfl⟩ := hwseg
    have hst : s ≤ t := hmax ⟨⟨ht.1.1.trans hs.1, hs.2⟩, hwS⟩
    have hEq : s = t := le_antisymm hst hs.1
    exact mem_singleton_iff.mpr (congrArg (lineMap a b) hEq)
  · exact singleton_subset_iff.mpr ⟨left_mem_segment ℝ q b, hq⟩

/-- A point on a finite polygonal chain can be reached by a finite prefix,
possibly cutting one original segment. The prefix retains the original first
vertex and its whole trace lies in the original trace. -/
theorem exists_polygonal_chain_prefix : ∀ {vs : List E} (hv : vs ≠ []) {q : E},
    q ∈ polygonalChain vs →
    ∃ us : List E, ∃ hu : us ≠ [], us.head hu = vs.head hv ∧
      us.getLast hu = q ∧ polygonalChain us ⊆ polygonalChain vs
  | [], hv, _, _ => (hv rfl).elim
  | [v], _, q, hq => by
    have hEq : q = v := mem_singleton_iff.mp hq
    exact ⟨[v], List.cons_ne_nil _ _, rfl, hEq.symm, subset_rfl⟩
  | u :: v :: rest, _, q, hq => by
    rcases hq with hfirst | htail
    · refine ⟨[u, q], List.cons_ne_nil _ _, rfl, rfl, ?_⟩
      intro w hw
      rcases hw with hw | hw
      · exact Or.inl ((convex_segment u v).segment_subset
          (left_mem_segment ℝ u v) hfirst hw)
      · exact Or.inl ((mem_singleton_iff.mp hw).symm ▸ hfirst)
    · obtain ⟨us, hu, hhead, hlast, hsub⟩ :=
        exists_polygonal_chain_prefix (List.cons_ne_nil v rest) htail
      refine ⟨u :: us, List.cons_ne_nil _ _, rfl, ?_, ?_⟩
      · rw [List.getLast_cons hu]
        exact hlast
      · cases us with
        | nil => exact (hu rfl).elim
        | cons w ws =>
          change w = v at hhead
          subst w
          exact union_subset_union subset_rfl hsub

/-- **Finite last-contact splice.** Appending an endpoint outside the old
trace admits a finite chain consisting of an old prefix followed by a fresh
terminal segment. That segment intersects the entire old trace exactly at
the splice vertex and its standard parametrization is injective. The new
chain keeps the original first endpoint and ends at the appended endpoint. -/
theorem exists_polygonal_chain_last_contact_splice {vs : List E} (hv : vs ≠ [])
    {b : E} (hb : b ∉ polygonalChain vs) :
    ∃ q ∈ polygonalChain vs, ∃ us : List E, ∃ hu : us ≠ [],
      us.head hu = vs.head hv ∧ us.getLast hu = q ∧
      polygonalChain us ⊆ polygonalChain vs ∧ q ≠ b ∧
      segment ℝ q b ∩ polygonalChain vs = {q} ∧
      Function.Injective (Path.segment q b) ∧
      polygonalChain (us ++ [b]) ⊆ polygonalChain (vs ++ [b]) ∧
      (us ++ [b]).head (List.append_ne_nil_of_left_ne_nil hu [b]) = vs.head hv ∧
      (us ++ [b]).getLast (List.append_ne_nil_of_left_ne_nil hu [b]) = b := by
  obtain ⟨q, hq, _, hqb, hseg, hmeet, hinj⟩ :=
    exists_last_contact_segment (isCompact_polygonal_chain vs)
      (getLast_mem_polygonal_chain hv) hb
  obtain ⟨us, hu, hhead, hlast, hsub⟩ := exists_polygonal_chain_prefix hv hq
  refine ⟨q, hq, us, hu, hhead, hlast, hsub, hqb, hmeet, hinj, ?_, ?_, ?_⟩
  · rw [polygonal_chain_concat hu, hlast, polygonal_chain_concat hv]
    exact union_subset_union hsub hseg
  · rw [List.head_append_of_ne_nil hu]
    exact hhead
  · exact List.getLast_append_singleton _

end LatticeProb.Topology
