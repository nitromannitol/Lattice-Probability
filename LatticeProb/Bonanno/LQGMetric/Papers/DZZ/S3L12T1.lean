/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12T1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S6

/-!
# DZZ Lemma 3.12, one-step claim: loop erasure and adjacent pairs (P2-DZZ312S)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1447–1453: `𝒞_{i+1}` is obtained by
replacing a segment of `𝒞_i`; the claim is stated for loop-free sequences (DEVIATIONS, P2-DZZ316),
so loops created by the replacement are erased. Own elementary list/walk bookkeeping:

* `pair_append_cons`: an adjacent pair of `P ++ x :: Q` is one of `P ++ [x]` or of `x :: Q`;
* `l312Bad_mono`: `ψ` is monotone in the set of adjacent pairs;
* **`l312_loop_erase`**: a `Neighbour`-chain of cells joining `u`, `v` contains a loop-free one
  (mathlib's `Walk.bypass`), not longer, with `ψ` only shrinking.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

lemma pair_append_cons {a b x : DyBox} :
    ∀ (P Q : List DyBox), [a, b] <:+: P ++ x :: Q → [a, b] <:+: P ++ [x] ∨ [a, b] <:+: x :: Q
  | [], Q, h => Or.inr h
  | p :: P', Q, h => by
    rw [List.cons_append, List.infix_cons_iff] at h
    rcases h with h | h
    · left
      obtain ⟨t, ht⟩ := h
      cases P' with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at ht
        obtain ⟨rfl, rfl, -⟩ := ht
        exact List.infix_refl _
      | cons q P'' =>
        simp only [List.cons_append, List.cons.injEq] at ht
        obtain ⟨rfl, rfl, -⟩ := ht
        exact (List.prefix_append [a, b] (P'' ++ [x])).isInfix
    · rcases pair_append_cons P' Q h with h' | h'
      · exact Or.inl (h'.trans (List.suffix_cons p _).isInfix)
      · exact Or.inr h'

lemma l312Bad_mono {ε : ℝ} {L L' : List DyBox} (hsub : ∀ c ∈ L', c ∈ L)
    (hpair : ∀ a b, [a, b] <:+: L' → [a, b] <:+: L ∨ [b, a] <:+: L) :
    l312Bad ε L' ⊆ l312Bad ε L := by
  intro c hc
  simp only [l312Bad, Finset.mem_filter, List.mem_toFinset] at hc ⊢
  obtain ⟨hcL, c', hp, hs⟩ := hc
  refine ⟨hsub c hcL, c', ?_, hs⟩
  rcases hp with h | h
  · rcases hpair _ _ h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  · rcases hpair _ _ h with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'

variable {m : DyBox → ℝ} {δ : ℝ}

lemma isChain_cellGraph_of : ∀ (L : List DyBox), L.IsChain Neighbour →
    (∀ c ∈ L, IsCell m δ c) → L.IsChain (cellGraph m δ).Adj
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.IsChain.singleton _
  | a :: b :: t, h, hc => by
    rw [List.isChain_cons_cons] at h ⊢
    exact ⟨⟨hc a (by simp), hc b (by simp), h.1⟩,
      isChain_cellGraph_of (b :: t) h.2 fun c hc' => hc c (List.mem_cons_of_mem _ hc')⟩

lemma exists_walk_of_isChain {G : SimpleGraph DyBox} :
    ∀ (L : List DyBox) (hL : L ≠ []), L.IsChain G.Adj →
      ∃ p : G.Walk (L.head hL) (L.getLast hL), p.support = L
  | [a], _, _ => ⟨SimpleGraph.Walk.nil, rfl⟩
  | a :: b :: t, _, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨q, hq⟩ := exists_walk_of_isChain (b :: t) (by simp) h.2
    exact ⟨SimpleGraph.Walk.cons h.1 q, congrArg (List.cons a) hq⟩

lemma edge_of_pair_support {G : SimpleGraph DyBox} {a b : DyBox} :
    ∀ {u v : DyBox} (p : G.Walk u v), [a, b] <:+: p.support → s(a, b) ∈ p.edges
  | _, _, .nil, h => by
    simp only [SimpleGraph.Walk.support_nil] at h
    have := h.length_le; simp at this
  | _, _, .cons hadj q, h => by
    rw [SimpleGraph.Walk.support_cons, List.infix_cons_iff] at h
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
    rcases h with h | h
    · left
      obtain ⟨t, ht⟩ := h
      rw [← SimpleGraph.Walk.cons_tail_support q] at ht
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, rfl, -⟩ := ht
      rfl
    · exact Or.inr (edge_of_pair_support q h)

lemma pair_of_edge_support {G : SimpleGraph DyBox} {a b : DyBox} :
    ∀ {u v : DyBox} (p : G.Walk u v), s(a, b) ∈ p.edges →
      [a, b] <:+: p.support ∨ [b, a] <:+: p.support
  | _, _, .nil, h => by simp at h
  | _, _, .cons hadj q, h => by
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at h
    rw [SimpleGraph.Walk.support_cons]
    rcases h with h | h
    · rw [Sym2.eq_iff] at h
      rw [← SimpleGraph.Walk.cons_tail_support q]
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (List.prefix_append [a, b] _).isInfix
      · exact Or.inr (List.prefix_append [b, a] _).isInfix
    · rcases pair_of_edge_support q h with h' | h'
      · exact Or.inl (h'.trans (List.suffix_cons _ _).isInfix)
      · exact Or.inr (h'.trans (List.suffix_cons _ _).isInfix)

/-- **Loop erasure** (DZZ's sequences are loop-free): a `Neighbour`-chain of cells joining `u`, `v`
contains a loop-free one, not longer, whose bad cells are bad in the original chain. -/
theorem l312_loop_erase {ε : ℝ} {u v : ℂ} {L : List DyBox} (hj : JoinsCells m δ u v L)
    (hch : L.IsChain Neighbour) :
    ∃ L' : List DyBox, JoinsCells m δ u v L' ∧ L'.IsChain Neighbour ∧ L'.Nodup ∧
      L'.length ≤ L.length ∧ l312Bad ε L' ⊆ l312Bad ε L := by
  obtain ⟨hne, hcells, hhead, hlast⟩ := hj
  obtain ⟨p, hp⟩ := exists_walk_of_isChain L hne (isChain_cellGraph_of L hch hcells)
  set q := p.bypass
  have hsub : ∀ c ∈ q.support, c ∈ L := fun c hc => hp ▸ p.support_bypass_subset_support hc
  refine ⟨q.support, ⟨by simp, fun c hc => hcells c (hsub c hc), ?_, ?_⟩,
    (SimpleGraph.Walk.isChain_adj_support q).imp fun a b h => h.2.2,
    (p.bypass_isPath).support_nodup, ?_, ?_⟩
  · rw [SimpleGraph.Walk.head_support]; exact hhead
  · rw [SimpleGraph.Walk.getLast_support]; exact hlast
  · have h1 := congrArg List.length hp
    rw [SimpleGraph.Walk.length_support] at h1
    rw [SimpleGraph.Walk.length_support]
    have : q.length ≤ p.length := SimpleGraph.Walk.length_bypass_le_length p
    omega
  · refine l312Bad_mono hsub fun a b h => ?_
    rw [← hp]
    exact pair_of_edge_support p (p.edges_bypass_subset_edges (edge_of_pair_support q h))

end DZZ
end LQGMetric
