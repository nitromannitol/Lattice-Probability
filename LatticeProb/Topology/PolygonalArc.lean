module

/-
# Injective polygonal arcs inside finite chain traces

The path of a finite chain is a finite concatenation of straight segment
paths. Geometric simplicity makes this path injective. Finite loop pruning
therefore extracts an actual polygonal arc with the original endpoints and
trace contained in the original chain, without any separation theorem.
-/
public import LatticeProb.Topology.SimplePolygonalChain

@[expose] public section



open Set unitInterval

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Concatenating two injective paths whose ranges meet only at the joining
point gives an injective path. -/
theorem path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X}
    {p : Path a b} {q : Path b c} (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : range p ∩ range q = {b}) : Function.Injective (p.trans q) := by
  intro s t h
  rw [Path.trans_apply, Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · apply Subtype.ext
    exact mul_left_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0) (congrArg Subtype.val (hp h))
  · have hpb : p ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ = b := by
      apply mem_singleton_iff.mp
      rw [← hmeet]
      exact ⟨⟨_, rfl⟩, ⟨_, h.symm⟩⟩
    have hqzero := hq (h.symm.trans (hpb.trans q.source.symm))
    have htzero : 2 * (t : ℝ) - 1 = 0 := congrArg Subtype.val hqzero
    have htHalf : (t : ℝ) ≤ 1 / 2 := by
      apply (le_div_iff₀ zero_lt_two).mpr
      rw [mul_comm, sub_eq_zero.mp htzero]
    exact (ht htHalf).elim
  · have hqb : q ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ = b := by
      apply mem_singleton_iff.mp
      rw [← hmeet]
      exact ⟨⟨_, h.symm⟩, ⟨_, rfl⟩⟩
    have hqzero := hq (hqb.trans q.source.symm)
    have hszero : 2 * (s : ℝ) - 1 = 0 := congrArg Subtype.val hqzero
    have hsHalf : (s : ℝ) ≤ 1 / 2 := by
      apply (le_div_iff₀ zero_lt_two).mpr
      rw [mul_comm, sub_eq_zero.mp hszero]
    exact (hs hsHalf).elim
  · apply Subtype.ext
    exact mul_left_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0)
      (sub_left_injective (congrArg Subtype.val (hq h)))

/-- The path of a finite vertex list follows each consecutive straight segment
in order. Its range is exactly the chain trace. A singleton gives a constant
path; the nonempty hypothesis excludes the empty list. -/
noncomputable def polygonalChainPath : (vs : List E) →
    (hv : vs ≠ []) → Path (vs.head hv) (vs.getLast hv)
  | [], hv => (hv rfl).elim
  | [a], _ => Path.refl a
  | [a, b], _ => Path.segment a b
  | a :: b :: c :: rest, _ => (Path.segment a b).trans
      (polygonalChainPath (b :: c :: rest) (List.cons_ne_nil _ _))

/-- The finite segment path has exactly the trace of its vertex list. -/
theorem range_polygonal_chain_path : ∀ (vs : List E) (hv : vs ≠ []),
    range (polygonalChainPath vs hv) = polygonalChain vs
  | [], hv => (hv rfl).elim
  | [a], _ => by
    change range (fun _ : unitInterval => a) = {a}
    exact range_const
  | [a, b], _ => by
    change range (Path.segment a b) = segment ℝ a b ∪ {b}
    rw [Path.range_segment]
    exact (union_eq_left.mpr (singleton_subset_iff.mpr (right_mem_segment ℝ a b))).symm
  | a :: b :: c :: rest, _ => by
    calc
      range (polygonalChainPath (a :: b :: c :: rest) _) =
          range ((Path.segment a b).trans
            (polygonalChainPath (b :: c :: rest) (List.cons_ne_nil _ _))) := rfl
      _ = range (Path.segment a b) ∪
          range (polygonalChainPath (b :: c :: rest) (List.cons_ne_nil _ _)) :=
        Path.trans_range _ _
      _ = segment ℝ a b ∪ polygonalChain (b :: c :: rest) :=
        congrArg₂ (· ∪ ·) (Path.range_segment a b) (range_polygonal_chain_path _ _)

/-- A simple chain with at least one edge has different first and last vertices. -/
theorem IsSimplePolygonalChain.head_ne_last {a b : E} {rest : List E}
    (hs : IsSimplePolygonalChain (a :: b :: rest)) :
    a ≠ (a :: b :: rest).getLast hs.ne_nil := by
  intro h
  have halast : a = (b :: rest).getLast hs.2.1.ne_nil := h.trans (List.getLast_cons _)
  have hamem : a ∈ polygonalChain (b :: rest) := halast ▸ getLast_mem_polygonal_chain _
  have hab : a = b := mem_singleton_iff.mp
    (le_of_eq hs.2.2 ⟨left_mem_segment ℝ a b, hamem⟩)
  exact hs.1 hab

/-- Geometric simplicity and distinct endpoints make the actual finite
segment path injective. -/
theorem IsSimplePolygonalChain.path_injective : ∀ {vs : List E}
    (hs : IsSimplePolygonalChain vs), vs.head hs.ne_nil ≠ vs.getLast hs.ne_nil →
    Function.Injective (polygonalChainPath vs hs.ne_nil)
  | [], hs, _ => hs.elim
  | [a], _, hne => (hne rfl).elim
  | [a, b], hs, _ => Path.segment_injective_of_ne hs.1
  | a :: b :: c :: rest, hs, _ => by
    rcases hs with ⟨hab, htail, hmeet⟩
    change Function.Injective ((Path.segment a b).trans
      (polygonalChainPath (b :: c :: rest) htail.ne_nil))
    apply path_trans_injective (Path.segment_injective_of_ne hab)
      (htail.path_injective htail.head_ne_last)
    calc
      range (Path.segment a b) ∩ range (polygonalChainPath (b :: c :: rest) _) =
          segment ℝ a b ∩ polygonalChain (b :: c :: rest) :=
        congrArg₂ (· ∩ ·) (Path.range_segment a b) (range_polygonal_chain_path _ _)
      _ = {b} := hmeet

/-- **Polygonal arc extraction.** A finite polygonal chain with distinct
endpoints contains a finite geometrically simple chain with the same endpoints.
Its explicit finite concatenation of segment paths is injective and its range
stays inside the original trace. Crossings, repeated vertices and overlaps are
all removed by finite last-contact induction. -/
theorem exists_injective_polygonal_arc (vs : List E) (hv : vs ≠ [])
    (hne : vs.head hv ≠ vs.getLast hv) :
    ∃ us : List E, ∃ hu : us ≠ [], IsSimplePolygonalChain us ∧
      us.head hu = vs.head hv ∧ us.getLast hu = vs.getLast hv ∧
      polygonalChain us ⊆ polygonalChain vs ∧
      Function.Injective (polygonalChainPath us hu) ∧
      range (polygonalChainPath us hu) = polygonalChain us := by
  obtain ⟨us, hu, hs, hhead, hlast, hsub⟩ := exists_simple_polygonal_chain vs hv
  have hneus : us.head hu ≠ us.getLast hu := by
    rw [hhead, hlast]
    exact hne
  exact ⟨us, hu, hs, hhead, hlast, hsub, hs.path_injective hneus,
    range_polygonal_chain_path us hu⟩

end LatticeProb.Topology
