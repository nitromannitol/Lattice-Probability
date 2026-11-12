/-
# Simple pieces of a sequence of polygonal chains

Let `σ 0, σ 1, …` be finite polygonal chains, each ending where the next one starts, such that chains
two or more steps apart are disjoint and the first vertex of `σ 0` is not on `σ 1`. Then there are
geometrically simple chains `L n ⊆ σ n`, each with at least two vertices, each ending where the next one
starts, such that consecutive pieces meet only at their common vertex and pieces two or more steps
apart are disjoint. The piece `L n` runs inside `σ n` from its starting point up to the first contact
with `σ (n + 1)`.
-/
import LatticeProb.Topology.PolygonalContact
import LatticeProb.Topology.SimplePolygonalChain

open Set

namespace LatticeProb.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A list whose first and last entries differ has at least two entries. -/
theorem two_le_length_of_head_ne_getLast {α : Type*} {l : List α} (hl : l ≠ [])
    (h : l.head hl ≠ l.getLast hl) : 2 ≤ l.length := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · exact absurd rfl hl
  · exact (h rfl).elim
  · simp

/-- **Simple piece up to the first contact.** Let `vs` be a finite chain whose last vertex lies on a
closed set `A`. From every point `p` of `vs`, a geometrically simple chain inside `vs` runs from `p` to
a point of `A` and meets `A` only at its last vertex. -/
theorem exists_simple_piece_to_first_contact {A : Set E} (hA : IsClosed A) {vs : List E}
    (hv : vs ≠ []) (hlast : vs.getLast hv ∈ A) {p : E} (hp : p ∈ polygonalChain vs) :
    ∃ us : List E, ∃ hu : IsSimplePolygonalChain us, us.head hu.ne_nil = p ∧
      polygonalChain us ⊆ polygonalChain vs ∧ polygonalChain us ∩ A = {us.getLast hu.ne_nil} := by
  obtain ⟨q, hq, ws, hw, hwh, hwl, hws, -⟩ :=
    exists_suffix_inter_eq_singleton (A := {p}) isClosed_singleton hv ⟨p, hp, rfl⟩
  rw [mem_singleton_iff] at hq
  have hwA : ws.getLast hw ∈ A := by rw [hwl]; exact hlast
  obtain ⟨r, hr, xs, hx, hxh, hxl, hxs, hxA⟩ :=
    exists_prefix_inter_eq_singleton hA hw ⟨ws.getLast hw, getLast_mem_polygonal_chain hw, hwA⟩
  obtain ⟨us, hu, hus, huh, hul, husx⟩ := exists_simple_polygonal_chain xs hx
  have hl : us.getLast hus.ne_nil = r := hul.trans hxl
  refine ⟨us, hus, huh.trans (hxh.trans (hwh.trans hq)), husx.trans (hxs.trans hws), ?_⟩
  rw [hl]
  apply subset_antisymm
  · exact (inter_subset_inter_left A husx).trans hxA.subset
  · rw [singleton_subset_iff]
    exact ⟨hl ▸ getLast_mem_polygonal_chain hus.ne_nil, hr⟩

/-- **Simple pieces of a sequence of chains.** Let `σ n` be finite polygonal chains, each ending where
the next one starts, with chains two or more steps apart disjoint and the first vertex of `σ 0` off
`σ 1`. Then there are geometrically simple chains `L n` with at least two vertices and traces inside
`σ n`, starting at the first vertex of `σ 0`, each ending where the next one starts, with consecutive
pieces meeting only at that common vertex and pieces two or more steps apart disjoint. -/
theorem exists_simple_pieces_of_chains (σ : ℕ → List E) (hσ : ∀ n, σ n ≠ [])
    (hjoin : ∀ n, (σ n).getLast (hσ n) = (σ (n + 1)).head (hσ (n + 1)))
    (hfar : ∀ n m, n + 2 ≤ m → Disjoint (polygonalChain (σ n)) (polygonalChain (σ m)))
    (h0 : (σ 0).head (hσ 0) ∉ polygonalChain (σ 1)) :
    ∃ L : ℕ → List E, ∃ hL : ∀ n, IsSimplePolygonalChain (L n),
      (L 0).head (hL 0).ne_nil = (σ 0).head (hσ 0) ∧ (∀ n, 2 ≤ (L n).length) ∧
      (∀ n, (L n).getLast (hL n).ne_nil = (L (n + 1)).head (hL (n + 1)).ne_nil) ∧
      (∀ n, polygonalChain (L n) ∩ polygonalChain (L (n + 1)) ⊆
        {(L (n + 1)).head (hL (n + 1)).ne_nil}) ∧
      (∀ n m, n + 2 ≤ m → Disjoint (polygonalChain (L n)) (polygonalChain (L m))) ∧
      ∀ n, polygonalChain (L n) ⊆ polygonalChain (σ n) := by
  have step : ∀ n, ∀ p : {x // x ∈ polygonalChain (σ n)}, ∃ us : List E,
      ∃ hu : IsSimplePolygonalChain us, us.head hu.ne_nil = p ∧
        polygonalChain us ⊆ polygonalChain (σ n) ∧
        polygonalChain us ∩ polygonalChain (σ (n + 1)) = {us.getLast hu.ne_nil} := fun n p =>
    exists_simple_piece_to_first_contact (isCompact_polygonal_chain _).isClosed (hσ n)
      (by rw [hjoin]; exact head_mem_polygonal_chain _) p.2
  choose M hM hMh hMs hMA using step
  have hlastmem : ∀ n p, (M n p).getLast (hM n p).ne_nil ∈ polygonalChain (σ (n + 1)) :=
    fun n p => ((hMA n p).symm.subset (mem_singleton _)).2
  let z : (n : ℕ) → {x // x ∈ polygonalChain (σ n)} := fun n =>
    Nat.rec (motive := fun n => {x // x ∈ polygonalChain (σ n)})
      ⟨(σ 0).head (hσ 0), head_mem_polygonal_chain _⟩
      (fun k p => ⟨(M k p).getLast (hM k p).ne_nil, hlastmem k p⟩) n
  have hz0 : (z 0 : E) = (σ 0).head (hσ 0) := rfl
  have hzs : ∀ n, (z (n + 1) : E) = (M n (z n)).getLast (hM n (z n)).ne_nil := fun n => rfl
  have hzmem : ∀ k, (z (k + 1) : E) ∈ polygonalChain (σ k) := fun k => by
    rw [hzs]; exact hMs k (z k) (getLast_mem_polygonal_chain _)
  have hjoinL : ∀ n, (M n (z n)).getLast (hM n (z n)).ne_nil =
      (M (n + 1) (z (n + 1))).head (hM (n + 1) (z (n + 1))).ne_nil := fun n =>
    ((hMh (n + 1) (z (n + 1))).trans (hzs n)).symm
  refine ⟨fun n => M n (z n), fun n => hM n (z n), (hMh 0 (z 0)).trans hz0, ?_, hjoinL, ?_,
    fun n m hnm => Disjoint.mono (hMs n (z n)) (hMs m (z m)) (hfar n m hnm),
    fun n => hMs n (z n)⟩
  · intro n
    apply two_le_length_of_head_ne_getLast (hM n (z n)).ne_nil
    rw [hMh, ← hzs]
    intro h
    rcases n with _ | k
    · apply h0
      rw [← hz0, h]
      exact (z 1).2
    · refine Set.disjoint_left.1 (hfar k (k + 2) le_rfl) (hzmem k) ?_
      rw [h]
      exact (z (k + 2)).2
  · intro n x hx
    have h1 : x ∈ polygonalChain (M n (z n)) ∩ polygonalChain (σ (n + 1)) :=
      ⟨hx.1, hMs (n + 1) (z (n + 1)) hx.2⟩
    rw [hMA, mem_singleton_iff] at h1
    exact h1.trans (hjoinL n)

end LatticeProb.Topology
