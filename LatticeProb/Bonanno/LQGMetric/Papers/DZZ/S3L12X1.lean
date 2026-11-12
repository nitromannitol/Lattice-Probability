/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W12
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P3

/-!
# DZZ Lemma 3.12: refining a coarse ring of boxes through the boundary rings (D99, P-6a)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.16
(l. 1381–1397: the boundary boxes `𝓑_∂(B', ε')` of the open boxes `B'` of the coarse enclosure
form the enclosure of `𝖢` at the fine scale) in the ring form of D93/D99: a cyclic
`Neighbour`-list of coarse boxes is refined to a cyclic `Neighbour`-list of fine boxes, the
concatenation of one covering walk of the boundary ring of each coarse box (in order).

* `ring_conn`, `ring_finite`, `ring_cover`: the boundary ring of a box is connected and finite,
  and has a covering walk between any two of its boxes;
* `ring_edge`: the rings of neighbouring boxes of one level contain neighbouring boxes;
* **`exists_ring_segs`**: the refinement of a coarse chain, segment by segment;
* `block_of_segs`: a block of the coarse list gives a block of the fine list.

Own elementary arguments (the ring walk of S3L316P3 kept in order), DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Relation

namespace LQGMetric
namespace DZZ

open DyBox

/-- The boundary ring of `b` is connected. -/
lemma ring_conn {d : ℕ} {b x y : DyBox} (hx : IsRingOf d b x) (hy : IsRingOf d b y) :
    ReflTransGen (ringRel {z | IsRingOf d b z}) x y := by
  have e : ringSet d [b] = {z | IsRingOf d b z} := by ext z; simp [ringSet]
  have h1 := ring_to_corner (l := [b]) List.mem_cons_self hx
  have h2 := ring_to_corner (l := [b]) List.mem_cons_self hy
  rw [e] at h1 h2
  exact h1.trans (ringRel_rtg_symm h2)

/-- The boundary ring of `b` is finite. -/
lemma ring_finite (d : ℕ) (b : DyBox) : {z | IsRingOf d b z}.Finite := by
  set L := b.n + d
  refine ((Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L)).image
    (fun q : ℕ × ℕ => fbox L q.1 q.2)).finite_toSet.subset ?_
  intro bt hr
  have hn : bt.n = L := hr.1
  have e : fbox L bt.j bt.k = bt := by rw [← hn]; exact fbox_self bt
  have hj := bt.hj; have hk := bt.hk
  rw [hn] at hj hk
  simp only [Finset.coe_image, Finset.coe_product, Finset.coe_range, Set.mem_image,
    Set.mem_prod, Set.mem_Iio, Prod.exists]
  exact ⟨bt.j, bt.k, ⟨hj, hk⟩, e⟩

/-- A covering walk of the boundary ring of `b` from `e` to `x`. -/
lemma ring_cover {d : ℕ} {b e x : DyBox} (he : IsRingOf d b e) (hx : IsRingOf d b x) :
    ∃ w : List DyBox, w.head? = some e ∧ w.getLast? = some x ∧ w.IsChain Neighbour ∧
      ∀ y, y ∈ w ↔ IsRingOf d b y := by
  set S := {z | IsRingOf d b z}
  have hfin : S.Finite := ring_finite d b
  obtain ⟨L1, hc1, hcov⟩ := exists_isChain_cover (U := S) (fun x hx y hy => ring_conn hx hy)
    hfin.toFinset.toList (fun z hz => by simpa using hz) e he
  set u := (e :: L1).getLast (List.cons_ne_nil _ _)
  have hu : IsRingOf d b u := mem_of_isChain_ringRel L1 e hc1 he u (List.getLast_mem _)
  obtain ⟨l2, hc2, hlast2⟩ := List.exists_isChain_cons_of_relationReflTransGen (ring_conn hu hx)
  have hsplit := List.dropLast_append_getLast (List.cons_ne_nil e L1)
  have ew : e :: (L1 ++ l2) = (e :: L1).dropLast ++ u :: l2 := by
    conv_lhs => rw [← List.cons_append, ← hsplit]
    rw [List.append_assoc, List.singleton_append]
  have hch : (e :: (L1 ++ l2)).IsChain (ringRel S) := by
    rw [ew, List.isChain_split, hsplit]; exact ⟨hc1, hc2⟩
  refine ⟨e :: (L1 ++ l2), rfl, ?_, hch.imp fun a b h => h.2.2, fun y => ⟨fun hy =>
    mem_of_isChain_ringRel _ e hch he y hy, fun hy => ?_⟩⟩
  · rw [ew, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hlast2]
  · rcases List.mem_cons.1 (hcov y (Finset.mem_toList.2 (hfin.mem_toFinset.2 hy))) with h | h
    · rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)

/-- An `r`-path leaving `A` has an edge leaving `A`. -/
lemma rtg_edge_out {α : Type*} {r : α → α → Prop} {A : Set α} {x y : α}
    (h : ReflTransGen r x y) (hx : x ∈ A) (hy : y ∉ A) : ∃ a b, a ∈ A ∧ b ∉ A ∧ r a b := by
  induction h with
  | refl => exact absurd hx hy
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ A
    · exact ⟨b, c, hb, hy, hbc⟩
    · exact ih hb

/-- The corner of `b'` is not a ring box of another box `b` of the same level. -/
lemma ringCorner_not_ring {d : ℕ} {b b' : DyBox} (hn : b'.n = b.n) (hne : b ≠ b') :
    ¬ IsRingOf d b (ringCorner d b') := by
  intro h
  obtain ⟨-, h1, h2, h3, h4, -⟩ := h
  obtain ⟨e1, e2⟩ := succ_mul_pow_le b' d
  have hp : 0 < 2 ^ d := Nat.two_pow_pos d
  have hx : b'.j * 2 ^ d < 2 ^ (b'.n + d) := by rw [add_mul] at e1; omega
  have hy : b'.k * 2 ^ d < 2 ^ (b'.n + d) := by rw [add_mul] at e2; omega
  unfold ringCorner at h1 h2 h3 h4
  rw [fbox_j hx hy] at h1 h2
  rw [fbox_k hx hy] at h3 h4
  have a1 : b.j ≤ b'.j := Nat.le_of_mul_le_mul_right h1 hp
  have a2 : b'.j < b.j + 1 := Nat.lt_of_mul_lt_mul_right (by omega : b'.j * 2 ^ d < (b.j + 1) * 2 ^ d)
  have a3 : b.k ≤ b'.k := Nat.le_of_mul_le_mul_right h3 hp
  have a4 : b'.k < b.k + 1 := Nat.lt_of_mul_lt_mul_right (by omega : b'.k * 2 ^ d < (b.k + 1) * 2 ^ d)
  exact hne (DyBox.ext hn.symm (by omega) (by omega))

/-- The boundary rings of neighbouring boxes of one level contain neighbouring boxes. -/
lemma ring_edge {d : ℕ} {b b' : DyBox} (hn : b'.n = b.n) (h : Neighbour b b') :
    ∃ x y, IsRingOf d b x ∧ IsRingOf d b' y ∧ Neighbour x y := by
  have hb : b ∈ [b, b'] := List.mem_cons_self
  have hb' : b' ∈ [b, b'] := by simp
  have hp : ReflTransGen (ringRel (ringSet d [b, b'])) (ringCorner d b) (ringCorner d b') := by
    rcases neighbour_idx hn.symm h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact corner_adj_j hb hb' hn h1 h2
    · exact ringRel_rtg_symm (corner_adj_j hb' hb hn.symm h1 h2.symm)
    · exact corner_adj_k hb hb' hn h1 h2
    · exact ringRel_rtg_symm (corner_adj_k hb' hb hn.symm h1 h2.symm)
  obtain ⟨x, y, hx, hy, hxy⟩ := rtg_edge_out (A := {z | IsRingOf d b z}) hp
    (ringCorner_mem (l := [b]) List.mem_cons_self |>.elim fun c hc => by
      rcases List.mem_singleton.1 hc.1 with rfl; exact hc.2)
    (ringCorner_not_ring hn h.1)
  obtain ⟨c, hc, hyc⟩ := hxy.2.1
  rcases List.mem_cons.1 hc with rfl | hc
  · exact absurd hyc hy
  · rw [List.mem_singleton.1 hc] at hyc
    exact ⟨x, y, hx, hyc, hxy.2.2⟩

/-- **Refinement of a coarse chain through the boundary rings**, segment by segment. -/
theorem exists_ring_segs (d : ℕ) : ∀ (t : List DyBox) (b e x : DyBox),
    (b :: t).IsChain Neighbour → (∀ c ∈ b :: t, c.n = b.n) → IsRingOf d b e →
    IsRingOf d ((b :: t).getLast (List.cons_ne_nil _ _)) x →
    ∃ P : List (DyBox × List DyBox), P.map Prod.fst = b :: t ∧
      (∀ p ∈ P, ∀ y, y ∈ p.2 ↔ IsRingOf d p.1 y) ∧
      (P.map Prod.snd).flatten.IsChain Neighbour ∧
      (P.map Prod.snd).flatten.head? = some e ∧ (P.map Prod.snd).flatten.getLast? = some x
  | [], b, e, x, _, _, he, hx => by
    obtain ⟨w, h1, h2, h3, h4⟩ := ring_cover he (by simpa using hx)
    refine ⟨[(b, w)], rfl, ?_, by simpa using h3, by simpa using h1, by simpa using h2⟩
    intro p hp; rw [List.mem_singleton.1 hp]; exact h4
  | c :: t, b, e, x, hch, hn, he, hx => by
    rw [List.isChain_cons_cons] at hch
    obtain ⟨a, a', ha, ha', haa⟩ := ring_edge (d := d) (hn c (by simp)) hch.1
    obtain ⟨P, h1, h2, h3, h4, h5⟩ := exists_ring_segs d t c a' x hch.2
      (fun z hz => (hn z (List.mem_cons_of_mem _ hz)).trans (hn c (by simp)).symm) ha'
      (by simpa using hx)
    obtain ⟨w, w1, w2, w3, w4⟩ := ring_cover he ha
    have hF : (P.map Prod.snd).flatten ≠ [] := by
      intro hF; rw [hF] at h4; simp at h4
    have hw : w ≠ [] := by intro hw; rw [hw] at w1; simp at w1
    refine ⟨(b, w) :: P, by simp [h1], ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact w4
      · exact h2 p hp
    · simp only [List.map_cons, List.flatten_cons]
      rw [List.isChain_append]
      refine ⟨w3, h3, fun u hu v hv => ?_⟩
      rw [w2] at hu; rw [h4] at hv
      cases hu; cases hv; exact haa
    · simp only [List.map_cons, List.flatten_cons]
      rw [List.head?_append_of_ne_nil _ hw, w1]
    · simp only [List.map_cons, List.flatten_cons]
      rw [List.getLast?_append_of_ne_nil _ hF, h5]

/-- A block of the coarse list gives a block of the refined list. -/
lemma block_of_segs {Q QF : DyBox → Prop} (P : List (DyBox × List DyBox))
    (hQ : ∀ p ∈ P, ∀ y ∈ p.2, QF y ↔ Q p.1) {L₁ L₂ L₃ : List DyBox}
    (hP : P.map Prod.fst = L₁ ++ L₂ ++ L₃) (h2 : ∀ c ∈ L₂, Q c) (h13 : ∀ c ∈ L₁ ++ L₃, ¬ Q c) :
    ∃ F₁ F₂ F₃ : List DyBox, (P.map Prod.snd).flatten = F₁ ++ F₂ ++ F₃ ∧
      (∀ y ∈ F₂, QF y) ∧ ∀ y ∈ F₁ ++ F₃, ¬ QF y := by
  obtain ⟨P12, P3, rfl, e12, e3⟩ := List.map_eq_append_iff.1 hP
  obtain ⟨P1, P2, rfl, e1, e2⟩ := List.map_eq_append_iff.1 e12
  refine ⟨(P1.map Prod.snd).flatten, (P2.map Prod.snd).flatten, (P3.map Prod.snd).flatten,
    by simp, ?_, ?_⟩
  · intro y hy
    obtain ⟨s, hs, hys⟩ := List.mem_flatten.1 hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    exact (hQ p (by simp [hp]) y hys).2 (h2 p.1 (by rw [← e2]; exact List.mem_map_of_mem hp))
  · intro y hy hQy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨s, hs, hys⟩ := List.mem_flatten.1 hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
      exact h13 p.1 (List.mem_append_left _ (by rw [← e1]; exact List.mem_map_of_mem hp))
        ((hQ p (by simp [hp]) y hys).1 hQy)
    · obtain ⟨s, hs, hys⟩ := List.mem_flatten.1 hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
      exact h13 p.1 (List.mem_append_right _ (by rw [← e3]; exact List.mem_map_of_mem hp))
        ((hQ p (by simp [hp]) y hys).1 hQy)

end DZZ
end LQGMetric
