/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12W8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12W7

/-!
# DZZ Lemma 3.12: choice of the segment (D93, packet P-8)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12, l. 1471–1488:
one of the two segments of the ring between `𝖢_{i,1}` and `𝖢_{i,2}` contains at most one
parent (D93: this replaces DZZ's "by connectivity", l. 1476–1477; every parent occurs once in
the ring, and the diagonal parent `𝖢_lt` has only `𝖢_lb`, `𝖢_rt` as ring neighbours).

* `succ_small`, `pred_small`: the cells of `𝒞_i` right after `𝖢_{i,1}` / before `𝖢_{i,2}`;
* `three_parents`: with three parents, one of them (the diagonal one) has only the two others
  as neighbouring cells meeting `𝖢_large`;
* **`pick_arc`**: unless `𝖢_{i,1}` and `𝖢_{i,2}` are both parents (Case 3), one of the two
  segments has at most one parent.

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

/-- The cell of `𝒞_i` right after `𝖢_{i,1}`. -/
lemma succ_small {N : ℕ} (hN : ∀ b, IsCell m δ b → b.n ≤ N) {C : DyBox} (hC : IsCell m δ C)
    (hCN : C.n + 1 ≤ N) {E : List DyBox} (hE : ∀ c ∈ E, IsCell m δ c)
    (henc : EnclosesBox C {c | c ∈ E}) {l A M B : List DyBox} {x y : DyBox}
    (hch : l.IsChain Neighbour) (hcells : ∀ c ∈ l, IsCell m δ c)
    (hl : l = A ++ x :: (M ++ y :: B)) (hCM : C ∈ M) (hM : ∀ c ∈ M, c ∉ E) :
    ∃ w, [x, w] <:+: l ∧ w ∉ E ∧ IsCell m δ w ∧ w.side ≤ C.side ∧
      (w.closedBox ∩ C.largeBox).Nonempty := by
  obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem hCM
  rcases M₁ with _ | ⟨w, M₁'⟩
  · refine ⟨C, ⟨A, M₂ ++ y :: B, by rw [hl]; simp⟩, hM C (by simp), hC, le_rfl,
      ⟨C.center, center_mem_closedBox' C, mem_largeBox_of_mem_self (center_mem_closedBox' C)⟩⟩
  set L := (w :: M₁' ++ [C]).reverse with hLdef
  have hLne : L ≠ [] := by simp [L]
  have hinf : w :: M₁' ++ [C] <:+: l := ⟨A ++ [x], M₂ ++ y :: B, by rw [hl]; simp⟩
  have hLch : L.IsChain Neighbour :=
    List.isChain_reverse.2 ((hch.infix hinf).imp fun a b h => Neighbour.symm h)
  have hLhead : L.head hLne = C := by simp [L]
  have hLlast : L.getLast hLne = w := by simp [L]
  have hsubL : ∀ c ∈ L, c ∈ w :: M₁' ++ C :: M₂ := by
    intro c hc; simp only [L, List.mem_reverse] at hc; simp only [List.mem_append,
      List.mem_cons, List.mem_singleton] at hc ⊢; tauto
  have hcellsL : ∀ c ∈ L, IsCell m δ c := fun c hc => hcells c (hinf.subset (by
    simp only [L, List.mem_reverse] at hc; exact hc))
  have hav : ∀ c ∈ L, c ∉ E := fun c hc => hM c (hsubL c hc)
  obtain ⟨h1, h2⟩ := chain_end_small hN hC hCN hE henc hLne hLch hcellsL hLhead hav
  rw [hLlast] at h1 h2
  exact ⟨w, ⟨A, M₁' ++ C :: M₂ ++ y :: B, by rw [hl]; simp⟩, hav w (by simp [L]),
    hcellsL w (by simp [L]), h1, h2⟩

/-- The cell of `𝒞_i` right before `𝖢_{i,2}`. -/
lemma pred_small {N : ℕ} (hN : ∀ b, IsCell m δ b → b.n ≤ N) {C : DyBox} (hC : IsCell m δ C)
    (hCN : C.n + 1 ≤ N) {E : List DyBox} (hE : ∀ c ∈ E, IsCell m δ c)
    (henc : EnclosesBox C {c | c ∈ E}) {l A M B : List DyBox} {x y : DyBox}
    (hch : l.IsChain Neighbour) (hcells : ∀ c ∈ l, IsCell m δ c)
    (hl : l = A ++ x :: (M ++ y :: B)) (hCM : C ∈ M) (hM : ∀ c ∈ M, c ∉ E) :
    ∃ w, [w, y] <:+: l ∧ w ∉ E ∧ IsCell m δ w ∧ w.side ≤ C.side ∧
      (w.closedBox ∩ C.largeBox).Nonempty := by
  obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem hCM
  rcases List.eq_nil_or_concat M₂ with rfl | ⟨M₂', w, rfl⟩
  · refine ⟨C, ⟨A ++ x :: M₁, B, by rw [hl]; simp⟩, hM C (by simp), hC, le_rfl,
      ⟨C.center, center_mem_closedBox' C, mem_largeBox_of_mem_self (center_mem_closedBox' C)⟩⟩
  set L := C :: M₂' ++ [w] with hLdef
  have hLne : L ≠ [] := by simp [L]
  have hinf : L <:+: l := ⟨A ++ x :: M₁, y :: B, by rw [hl]; simp [L]⟩
  have hLch : L.IsChain Neighbour := hch.infix hinf
  have hLhead : L.head hLne = C := by simp [L]
  have hLlast : L.getLast hLne = w := by simp [L]
  have hcellsL : ∀ c ∈ L, IsCell m δ c := fun c hc => hcells c (hinf.subset hc)
  have hav : ∀ c ∈ L, c ∉ E := fun c hc => hM c (by
    simp only [L, List.mem_append, List.mem_cons, List.mem_singleton] at hc ⊢
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]; tauto)
  obtain ⟨h1, h2⟩ := chain_end_small hN hC hCN hE henc hLne hLch hcellsL hLhead hav
  rw [hLlast] at h1 h2
  exact ⟨w, ⟨A ++ x :: M₁ ++ C :: M₂', B, by rw [hl]; simp⟩, hav w (by simp [L]),
    hcellsL w (by simp [L]), h1, h2⟩

/-- **Three parents**: one of them (the diagonal one) has only the two others as neighbouring
cells meeting `𝖢_large`. -/
lemma three_parents {C a b c : DyBox} (hC : IsCell m δ C) (ha : IsParent m δ C a)
    (hb : IsParent m δ C b) (hc : IsParent m δ C c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (∀ z, IsCell m δ z → Neighbour a z → (z.closedBox ∩ C.largeBox).Nonempty →
        z = b ∨ z = c) ∨
      (∀ z, IsCell m δ z → Neighbour b z → (z.closedBox ∩ C.largeBox).Nonempty →
        z = a ∨ z = c) ∨
      (∀ z, IsCell m δ z → Neighbour c z → (z.closedBox ∩ C.largeBox).Nonempty →
        z = a ∨ z = b) := by
  obtain ⟨Qa, qa, sa⟩ := exists_quad_of_parent hC ha.1 ha.2.1 ha.2.2
  obtain ⟨Qb, qb, sb⟩ := exists_quad_of_parent hC hb.1 hb.2.1 hb.2.2
  obtain ⟨Qc, qc, sc⟩ := exists_quad_of_parent hC hc.1 hc.2.1 hc.2.2
  have c1 : qcode C Qa ≠ qcode C Qb := fun e =>
    quad_ne_of_parent_ne ha hb hab qa sa sb (quad_eq_of_qcode qa qb e)
  have c2 : qcode C Qa ≠ qcode C Qc := fun e =>
    quad_ne_of_parent_ne ha hc hac qa sa sc (quad_eq_of_qcode qa qc e)
  have c3 : qcode C Qb ≠ qcode C Qc := fun e =>
    quad_ne_of_parent_ne hb hc hbc qb sb sc (quad_eq_of_qcode qb qc e)
  have := qcode_lt C Qa; have := qcode_lt C Qb; have := qcode_lt C Qc
  have key : qcode C Qa = 2 ∨ qcode C Qb = 2 ∨ qcode C Qc = 2 := by omega
  rcases key with h | h | h
  · exact Or.inl fun z hz hn hzL => diag_nbr hC ha hb hc hab hac hbc qa sa h hz hn hzL
  · exact Or.inr (Or.inl fun z hz hn hzL =>
      diag_nbr hC hb ha hc hab.symm hbc hac qb sb h hz hn hzL)
  · refine Or.inr (Or.inr fun z hz hn hzL => ?_)
    exact diag_nbr hC hc ha hb hac.symm hbc.symm hab qc sc h hz hn hzL

end DZZ
end LQGMetric
