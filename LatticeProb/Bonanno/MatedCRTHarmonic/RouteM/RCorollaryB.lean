/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.RCorollaryB at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Core.CellInterfaces

/-!
# Route M, Corollary B′: connectivity of the cells met by a connected set

If the cells through every point induce a connected subgraph (TF2's property (LC), the Core interface
`CellularEmbedding.PointConnected`, proved for the mated-CRT map by TF2's Theorem B), then for every connected
`S ⊆ ℂ` the vertices whose cells meet `S` induce a connected subgraph of `G.adj`
(`connected_induce_verticesMeeting`). Proof (TF2 §5): a separation of `V(S)` into two non-adjacent parts would give
two closed sets (locally finite unions of compact cells) covering `S`; connectedness of `S` makes them meet at a point
`q`, and (LC) at `q` joins the two parts.

The walk form `exists_walk_support_verticesMeeting` is what Lemma R consumes: two vertices whose cells meet `S` are
joined by a walk of `G.adj` all of whose vertices have cells meeting `S`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace MatedCRTHarmonic.RouteM

variable {V E : Type*} {G : LFMultigraph V E} {o : V} {H : CellularEmbedding G o}

/-- Every point of the plane lies in some cell. -/
theorem exists_mem_cell_of_cover (H : CellularEmbedding G o) (q : ℂ) : ∃ x, q ∈ H.cell x := by
  have hq : q ∈ ⋃ x, H.cell x := by rw [H.iUnion_cell]; exact mem_univ q
  simpa using hq

/-- A union of a subfamily of cells is closed (local finiteness, compact cells). -/
theorem isClosed_iUnion_cell_subtype (H : CellularEmbedding G o) (A : Set V) :
    IsClosed (⋃ x : A, H.cell x) :=
  (H.locallyFinite_cell.comp_injective Subtype.val_injective).isClosed_iUnion fun x =>
    (H.isCompact_cell x).isClosed

/-- **Corollary B′** (TF2 §5): under (LC), for every connected `S ⊆ ℂ` the vertices whose cells meet `S` induce a
connected subgraph of `G.adj`. -/
theorem connected_induce_verticesMeeting (hLC : H.PointConnected) {S : Set ℂ} (hS : IsConnected S) :
    (G.adj.induce (verticesMeeting H.cell S)).Connected := by
  classical
  set W := verticesMeeting H.cell S with hW
  obtain ⟨q₀, hq₀S⟩ := hS.nonempty
  obtain ⟨x₀, hx₀⟩ := exists_mem_cell_of_cover H q₀
  have hx₀W : x₀ ∈ W := ⟨q₀, hx₀, hq₀S⟩
  set a₀ : W := ⟨x₀, hx₀W⟩ with ha₀
  -- every vertex of `W` is reachable from `a₀`
  have hall : ∀ b : W, (G.adj.induce W).Reachable a₀ b := by
    by_contra hnot
    obtain ⟨b₁, hb₁⟩ := not_forall.1 hnot
    set A : Set V := {x | ∃ hx : x ∈ W, (G.adj.induce W).Reachable a₀ ⟨x, hx⟩} with hA
    set B : Set V := {x | x ∈ W ∧ x ∉ A} with hB
    have hAc : IsClosed (⋃ x : A, H.cell x) := isClosed_iUnion_cell_subtype H A
    have hBc : IsClosed (⋃ x : B, H.cell x) := isClosed_iUnion_cell_subtype H B
    have hcover : S ⊆ (⋃ x : A, H.cell x) ∪ (⋃ x : B, H.cell x) := by
      intro q hq
      obtain ⟨x, hx⟩ := exists_mem_cell_of_cover H q
      have hxW : x ∈ W := ⟨q, hx, hq⟩
      by_cases hxA : x ∈ A
      · exact Or.inl (mem_iUnion.2 ⟨⟨x, hxA⟩, hx⟩)
      · exact Or.inr (mem_iUnion.2 ⟨⟨x, hxW, hxA⟩, hx⟩)
    have hSA : (S ∩ ⋃ x : A, H.cell x).Nonempty :=
      ⟨q₀, hq₀S, mem_iUnion.2 ⟨⟨x₀, hx₀W, SimpleGraph.Reachable.refl _⟩, hx₀⟩⟩
    have hb₁A : (b₁ : V) ∉ A := by
      rintro ⟨hb, hreach⟩
      exact hb₁ hreach
    obtain ⟨q₁, hq₁cell, hq₁S⟩ := b₁.2
    have hSB : (S ∩ ⋃ x : B, H.cell x).Nonempty :=
      ⟨q₁, hq₁S, mem_iUnion.2 ⟨⟨b₁, b₁.2, hb₁A⟩, hq₁cell⟩⟩
    obtain ⟨q, hqS, hqA, hqB⟩ :=
      isPreconnected_closed_iff.1 hS.isPreconnected _ _ hAc hBc hcover hSA hSB
    obtain ⟨⟨a, haW, hreach_a⟩, hqa⟩ := mem_iUnion.1 hqA
    obtain ⟨⟨b, hbW, hbA⟩, hqb⟩ := mem_iUnion.1 hqB
    -- (LC) at `q` joins `a` to `b` through cells containing `q`, all of which meet `S`
    have hsub : {x | q ∈ H.cell x} ≤ W := fun x hx => ⟨q, hx, hqS⟩
    have hreach_q : (G.adj.induce {x | q ∈ H.cell x}).Reachable ⟨a, hqa⟩ ⟨b, hqb⟩ :=
      (hLC q).preconnected _ _
    have hreach_ab : (G.adj.induce W).Reachable ⟨a, haW⟩ ⟨b, hbW⟩ :=
      hreach_q.map (G.adj.induceHomOfLE hsub).toHom
    exact hbA ⟨hbW, hreach_a.trans hreach_ab⟩
  have : Nonempty W := ⟨a₀⟩
  exact ⟨fun u v => (hall u).symm.trans (hall v)⟩

/-- Walk form of Corollary B′: two vertices whose cells meet a connected set `S` are joined by a walk of `G.adj`
all of whose vertices have cells meeting `S`. -/
theorem exists_walk_support_verticesMeeting (hLC : H.PointConnected) {S : Set ℂ} (hS : IsConnected S)
    {a b : V} (ha : a ∈ verticesMeeting H.cell S) (hb : b ∈ verticesMeeting H.cell S) :
    ∃ w : G.adj.Walk a b, ∀ y ∈ w.support, y ∈ verticesMeeting H.cell S := by
  obtain ⟨p⟩ := (connected_induce_verticesMeeting hLC hS).preconnected ⟨a, ha⟩ ⟨b, hb⟩
  set f := (SimpleGraph.Embedding.induce (verticesMeeting H.cell S)).toHom with hf
  have key : ∀ y ∈ (p.map f).support, y ∈ verticesMeeting H.cell S := by
    intro y hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨y', _, rfl⟩ := hy
    exact y'.2
  exact ⟨p.map f, key⟩

end MatedCRTHarmonic.RouteM
