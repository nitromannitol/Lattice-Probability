/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W6

/-!
# DZZ Lemma 3.12: the two segments of the ring, and the cells next to `𝖢_{i,1}`, `𝖢_{i,2}`
(D93, packet P-8)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1471–1473
("divide `𝒞_{i,cross}` into two segments with respective ending cells `𝖢_{i,1}` and `𝖢_{i,2}`")
and l. 1491–1492 (`s_{𝖢_{i,j}} ≤ s_𝖢/ε*` by maximality of `𝖢`).

* `exists_arcs`: the two arcs of a cyclic `Neighbour`-list between two of its cells;
* `parent_out`: a parent has a point outside `𝖢_large`;
* **`chain_end_small`**: a chain from `𝖢` avoiding the enclosure ends in a cell of side `≤ s_𝖢`
  meeting `𝖢_large` (`exists_mem_enc_of_chain`).

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- A cyclic `Neighbour`-list. -/
def CycChain (Z : List DyBox) : Prop :=
  Z.IsChain Neighbour ∧ ∀ a ∈ Z.getLast?, ∀ b ∈ Z.head?, Neighbour a b

lemma cycChain_rotate {Z₁ Z₂ : List DyBox} (h : CycChain (Z₁ ++ Z₂)) : CycChain (Z₂ ++ Z₁) := by
  rcases List.eq_nil_or_concat Z₁ with rfl | ⟨L₁, a₁, rfl⟩
  · simpa using h
  rcases Z₂ with _ | ⟨b₂, T₂⟩
  · simpa using h
  obtain ⟨hch, hcyc⟩ := h
  rw [List.isChain_append] at hch
  obtain ⟨h1, h2, h12⟩ := hch
  refine ⟨List.isChain_append.2 ⟨h2, h1, ?_⟩, ?_⟩
  · intro a ha b hb
    apply hcyc a (by simpa [List.getLast?_append] using ha) b
    rcases L₁ with _ | ⟨c, L₁⟩ <;> simpa using hb
  · intro a ha b hb
    simp only [List.concat_eq_append] at ha
    rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_append_of_ne_nil _ (by simp)] at ha
    simp at ha hb
    subst ha hb
    exact h12 a₁ (by simp) b₂ (by simp)

/-- **The two segments** (DZZ l. 1471–1473): arcs of a cyclic list between two distinct
elements, together a permutation of the list. -/
theorem exists_arcs {Z : List DyBox} (hZ : CycChain Z) {x y : DyBox} (hx : x ∈ Z) (hy : y ∈ Z)
    (hxy : x ≠ y) :
    ∃ R₁ R₂ : List DyBox, (x :: R₁ ++ [y]).IsChain Neighbour ∧
      (x :: R₂ ++ [y]).IsChain Neighbour ∧ (R₁ ++ R₂ ++ [x, y]).Perm Z := by
  obtain ⟨Z₁, Z₂, rfl⟩ := List.append_of_mem hx
  have hrot : CycChain (x :: (Z₂ ++ Z₁)) := by
    simpa using cycChain_rotate (Z₁ := Z₁) (Z₂ := x :: Z₂) hZ
  have hyT : y ∈ Z₂ ++ Z₁ := by
    simp only [List.mem_append, List.mem_cons] at hy ⊢
    rcases hy with hy | hy | hy
    · exact Or.inr hy
    · exact absurd hy.symm hxy
    · exact Or.inl hy
  obtain ⟨P, S, hPS⟩ := List.append_of_mem hyT
  rw [hPS] at hrot
  obtain ⟨hch, hcyc⟩ := hrot
  have hsplit := (List.isChain_split (l₁ := x :: P) (c := y) (l₂ := S)).1 (by simpa using hch)
  refine ⟨P, S.reverse, by simpa using hsplit.1, ?_, ?_⟩
  · have h2 : (y :: S ++ [x]).IsChain Neighbour := by
      rw [List.isChain_append]
      refine ⟨hsplit.2, List.isChain_singleton _, fun a ha b hb => ?_⟩
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst hb
      apply hcyc a _ x (by simp)
      have e : (x :: (P ++ y :: S)).getLast? = (y :: S).getLast? := by
        rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rw [e]
      simpa [List.getLast?_append] using ha
    have h3 := List.isChain_reverse.2 (h2.imp fun a b h => Neighbour.symm h)
    simpa using h3
  · have e : Z₁ ++ x :: Z₂ = Z₁ ++ x :: Z₂ := rfl
    rw [List.perm_iff_count]
    intro a
    have hc := congrArg (List.count a) hPS
    simp only [List.count_append, List.count_cons, List.count_reverse, List.count_nil] at hc ⊢
    omega

/-- A parent has a point (in the sense of `Mem`) outside `𝖢_large`: the centre of its
quadrant box. -/
lemma parent_out {C P : DyBox} (hC : IsCell m δ C) (hP : IsParent m δ C P) :
    ∃ v, P.Mem v ∧ v ∉ C.largeBox := by
  obtain ⟨Q, hQ, hQP⟩ := exists_quad_of_parent hC hP.1 hP.2.1 hP.2.2
  obtain ⟨q1, a1, a2, a3, a4, a5⟩ := quad_facts hQ
  have hPn := n_lt_of_side_lt hP.2.1
  refine ⟨Q.center, ⟨closedBox_sub_dzzV' Q (center_mem_closedBox' Q), ?_⟩, ?_⟩
  · rw [← anc_boxAt (show P.n ≤ Q.n by omega), boxAt_center_self]
    exact anc_eq_of_sub rfl (by omega) hQP
  · intro hL
    simp only [DyBox.largeBox, mem_ofPred_eq, abs_le, DyBox.center] at hL
    have hs : Q.side = 2 * C.side := by
      unfold DyBox.side; rw [← q1, pow_succ]; field_simp
    have hCs := C.side_pos'
    rw [hs] at hL
    obtain ⟨⟨b1, b2⟩, b3, b4⟩ := hL
    rcases a5 with h | h
    · have : (2 * Q.j + 2 ≤ C.j) ∨ (C.j + 1 ≤ 2 * Q.j) := by omega
      rcases this with h' | h'
      · have : ((2 * Q.j + 2 : ℕ) : ℝ) ≤ C.j := by exact_mod_cast h'
        push_cast at this; nlinarith
      · have : ((C.j + 1 : ℕ) : ℝ) ≤ ((2 * Q.j : ℕ) : ℝ) := by exact_mod_cast h'
        push_cast at this; nlinarith
    · have : (2 * Q.k + 2 ≤ C.k) ∨ (C.k + 1 ≤ 2 * Q.k) := by omega
      rcases this with h' | h'
      · have : ((2 * Q.k + 2 : ℕ) : ℝ) ≤ C.k := by exact_mod_cast h'
        push_cast at this; nlinarith
      · have : ((C.k + 1 : ℕ) : ℝ) ≤ ((2 * Q.k : ℕ) : ℝ) := by exact_mod_cast h'
        push_cast at this; nlinarith

/-- **The cells next to `𝖢_{i,1}`, `𝖢_{i,2}` inside the enclosure are small** (DZZ l. 1491):
a chain of cells from `𝖢` none of which is in the enclosure ends in a cell of side `≤ s_𝖢`
meeting `𝖢_large`. -/
theorem chain_end_small {N : ℕ} (hN : ∀ b, IsCell m δ b → b.n ≤ N) {C : DyBox}
    (hC : IsCell m δ C) (hCN : C.n + 1 ≤ N) {E : List DyBox} (hE : ∀ c ∈ E, IsCell m δ c)
    (henc : EnclosesBox C {c | c ∈ E}) {L : List DyBox} (hne : L ≠ [])
    (hch : L.IsChain Neighbour) (hcells : ∀ c ∈ L, IsCell m δ c) (hhead : L.head hne = C)
    (hav : ∀ c ∈ L, c ∉ E) :
    (L.getLast hne).side ≤ C.side ∧ ((L.getLast hne).closedBox ∩ C.largeBox).Nonempty := by
  have hw := hcells _ (List.getLast_mem hne)
  have hmeet : ((L.getLast hne).closedBox ∩ C.largeBox).Nonempty := by
    by_contra hno
    have hv : (L.getLast hne).Mem (L.getLast hne).center :=
      ⟨closedBox_sub_dzzV' _ (center_mem_closedBox' _), boxAt_center_self _⟩
    obtain ⟨c, hc, hcE⟩ := exists_mem_enc_of_chain hN hCN hE henc hne hch hcells hhead hv
      (fun h => hno ⟨_, center_mem_closedBox' _, h⟩)
    exact hav c hc hcE
  refine ⟨?_, hmeet⟩
  by_contra hs; push Not at hs
  obtain ⟨v, hv, hvL⟩ := parent_out hC ⟨hw, hs, hmeet⟩
  obtain ⟨c, hc, hcE⟩ := exists_mem_enc_of_chain hN hCN hE henc hne hch hcells hhead hv hvL
  exact hav c hc hcE

end DZZ
end LQGMetric
