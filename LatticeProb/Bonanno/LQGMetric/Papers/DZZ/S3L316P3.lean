/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L316P3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P2

/-!
# DZZ Lemma 3.16: boundary boxes of enclosing boxes enclose (P2-DZZ316), part 2

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1393–1397 (implicit in DZZ; own
elementary argument): if `B'_1, …, B'_d ∈ 𝓑(B, 2^{-k})` enclose `B` and every box of
`𝓑_∂(B'_i, 2^{-d})` is good, then good boxes of `𝓑(B, 2^{-(k+d)})` enclose `B`
(`hasEnclosure_ring`). The new sequence runs through the boundary rings of the `B'_i`:
each ring is `Neighbour`-connected, rings of neighbouring `B'_i` are connected, and a path from
`B` to `∂B_large` meeting `B'_i` meets `∂B'_i`, hence a ring box.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Relation

namespace LQGMetric
namespace DZZ

open DyBox

/-- The ring boxes (depth `d`) of all boxes of `l`. -/
def ringSet (d : ℕ) (l : List DyBox) : Set DyBox := {bt | ∃ b ∈ l, IsRingOf d b bt}

/-- Neighbouring steps inside `S`. -/
def ringRel (S : Set DyBox) (a b : DyBox) : Prop := a ∈ S ∧ b ∈ S ∧ Neighbour a b

/-- The lower-left ring box of `b`. -/
def ringCorner (d : ℕ) (b : DyBox) : DyBox := fbox (b.n + d) (b.j * 2 ^ d) (b.k * 2 ^ d)

lemma ringRel_rtg_symm {S : Set DyBox} {a b : DyBox} (h : ReflTransGen (ringRel S) a b) :
    ReflTransGen (ringRel S) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

variable {d : ℕ} {l : List DyBox}

lemma ringCorner_mem {b : DyBox} (hb : b ∈ l) : ringCorner d b ∈ ringSet d l := by
  have hN : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  exact ⟨b, hb, isRingOf_fbox le_rfl (by rw [add_mul]; omega) le_rfl (by rw [add_mul]; omega)
    (Or.inl rfl)⟩

/-- Walking along a horizontal edge row of the ring of `b`. -/
lemma ring_row_walk {b : DyBox} (hb : b ∈ l) {y : ℕ} (hy1 : b.k * 2 ^ d ≤ y)
    (hy2 : y + 1 ≤ (b.k + 1) * 2 ^ d) (hyr : y = b.k * 2 ^ d ∨ y + 1 = (b.k + 1) * 2 ^ d) :
    ∀ x, b.j * 2 ^ d ≤ x → x + 1 ≤ (b.j + 1) * 2 ^ d →
      ReflTransGen (ringRel (ringSet d l)) (fbox (b.n + d) x y)
        (fbox (b.n + d) (b.j * 2 ^ d) y) := by
  obtain ⟨e1, e2⟩ := succ_mul_pow_le b d
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => intro _; exact .refl
  | succ x hx ih =>
    intro hx2
    have hm : ∀ x', b.j * 2 ^ d ≤ x' → x' + 1 ≤ (b.j + 1) * 2 ^ d →
        fbox (b.n + d) x' y ∈ ringSet d l := fun x' h1 h2 =>
      ⟨b, hb, isRingOf_fbox h1 h2 hy1 hy2 (Or.inr (Or.inr hyr))⟩
    refine ReflTransGen.head ⟨hm _ (by omega) hx2, hm _ hx (by omega), ?_⟩ (ih (by omega))
    exact (neighbour_fbox_j (by omega) (by omega)).symm

/-- Walking along a vertical edge column of the ring of `b`. -/
lemma ring_col_walk {b : DyBox} (hb : b ∈ l) {x : ℕ} (hx1 : b.j * 2 ^ d ≤ x)
    (hx2 : x + 1 ≤ (b.j + 1) * 2 ^ d) (hxr : x = b.j * 2 ^ d ∨ x + 1 = (b.j + 1) * 2 ^ d) :
    ∀ y, b.k * 2 ^ d ≤ y → y + 1 ≤ (b.k + 1) * 2 ^ d →
      ReflTransGen (ringRel (ringSet d l)) (fbox (b.n + d) x y)
        (fbox (b.n + d) x (b.k * 2 ^ d)) := by
  obtain ⟨e1, e2⟩ := succ_mul_pow_le b d
  intro y hy
  induction y, hy using Nat.le_induction with
  | base => intro _; exact .refl
  | succ y hy ih =>
    intro hy2
    have hm : ∀ y', b.k * 2 ^ d ≤ y' → y' + 1 ≤ (b.k + 1) * 2 ^ d →
        fbox (b.n + d) x y' ∈ ringSet d l := fun y' h1 h2 => by
      refine ⟨b, hb, isRingOf_fbox hx1 hx2 h1 h2 ?_⟩
      rcases hxr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    refine ReflTransGen.head ⟨hm _ (by omega) hy2, hm _ hy (by omega), ?_⟩ (ih (by omega))
    exact (neighbour_fbox_k (by omega) (by omega)).symm

/-- Every ring box of `b` is connected to the corner of `b`. -/
lemma ring_to_corner {b bt : DyBox} (hb : b ∈ l) (h : IsRingOf d b bt) :
    ReflTransGen (ringRel (ringSet d l)) bt (ringCorner d b) := by
  have e : fbox (b.n + d) bt.j bt.k = bt := by rw [← h.1]; exact fbox_self bt
  rw [← e]
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  have hN : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have c1 : b.j * 2 ^ d + 1 ≤ (b.j + 1) * 2 ^ d := by rw [add_mul]; omega
  have c2 : b.k * 2 ^ d + 1 ≤ (b.k + 1) * 2 ^ d := by rw [add_mul]; omega
  unfold ringCorner
  rcases h5 with h | h | h | h
  · rw [h]; exact ring_col_walk hb le_rfl c1 (Or.inl rfl) _ h3 h4
  · exact (ring_col_walk hb h1 h2 (Or.inr h) _ h3 h4).trans
      (ring_row_walk hb le_rfl c2 (Or.inl rfl) _ h1 h2)
  · rw [h]; exact ring_row_walk hb le_rfl c2 (Or.inl rfl) _ h1 h2
  · exact (ring_row_walk hb h3 h4 (Or.inr h) _ h1 h2).trans
      (ring_col_walk hb le_rfl c1 (Or.inl rfl) _ h3 h4)

/-- Corners of horizontally adjacent boxes are connected. -/
lemma corner_adj_j {b₁ b₂ : DyBox} (hb₁ : b₁ ∈ l) (hb₂ : b₂ ∈ l) (hn : b₂.n = b₁.n)
    (hj : b₂.j = b₁.j + 1) (hk : b₂.k = b₁.k) :
    ReflTransGen (ringRel (ringSet d l)) (ringCorner d b₁) (ringCorner d b₂) := by
  have hN : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  obtain ⟨e1, e2⟩ := succ_mul_pow_le b₁ d
  set X := (b₁.j + 1) * 2 ^ d - 1
  have hX1 : b₁.j * 2 ^ d ≤ X := by simp only [X, add_mul]; omega
  have hX2 : X + 1 = (b₁.j + 1) * 2 ^ d := by simp only [X, add_mul]; omega
  have c2 : b₁.k * 2 ^ d + 1 ≤ (b₁.k + 1) * 2 ^ d := by rw [add_mul]; omega
  have w := ringRel_rtg_symm (ring_row_walk hb₁ le_rfl c2 (Or.inl rfl) X hX1 hX2.le)
  have e : ringCorner d b₂ = fbox (b₁.n + d) (X + 1) (b₁.k * 2 ^ d) := by
    unfold ringCorner; rw [hn, hj, hk, hX2]
  refine w.tail ⟨⟨b₁, hb₁, isRingOf_fbox hX1 hX2.le le_rfl c2 (Or.inr (Or.inl hX2))⟩,
    ringCorner_mem hb₂, ?_⟩
  have e3 := (succ_mul_pow_le b₂ d).1
  rw [hn, hj, add_mul (b₁.j + 1) 1, one_mul] at e3
  rw [e]
  refine neighbour_fbox_j ?_ ?_
  · generalize (b₁.j + 1) * 2 ^ d = A at *; omega
  · generalize (b₁.k + 1) * 2 ^ d = A at *; omega

/-- Corners of vertically adjacent boxes are connected. -/
lemma corner_adj_k {b₁ b₂ : DyBox} (hb₁ : b₁ ∈ l) (hb₂ : b₂ ∈ l) (hn : b₂.n = b₁.n)
    (hk : b₂.k = b₁.k + 1) (hj : b₂.j = b₁.j) :
    ReflTransGen (ringRel (ringSet d l)) (ringCorner d b₁) (ringCorner d b₂) := by
  have hN : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  obtain ⟨e1, e2⟩ := succ_mul_pow_le b₁ d
  set Y := (b₁.k + 1) * 2 ^ d - 1
  have hY1 : b₁.k * 2 ^ d ≤ Y := by simp only [Y, add_mul]; omega
  have hY2 : Y + 1 = (b₁.k + 1) * 2 ^ d := by simp only [Y, add_mul]; omega
  have c1 : b₁.j * 2 ^ d + 1 ≤ (b₁.j + 1) * 2 ^ d := by rw [add_mul]; omega
  have w := ringRel_rtg_symm (ring_col_walk hb₁ le_rfl c1 (Or.inl rfl) Y hY1 hY2.le)
  have e : ringCorner d b₂ = fbox (b₁.n + d) (b₁.j * 2 ^ d) (Y + 1) := by
    unfold ringCorner; rw [hn, hj, hk, hY2]
  refine w.tail ⟨⟨b₁, hb₁, isRingOf_fbox le_rfl c1 hY1 hY2.le (Or.inr (Or.inr (Or.inr hY2)))⟩,
    ringCorner_mem hb₂, ?_⟩
  have e3 := (succ_mul_pow_le b₂ d).2
  rw [hn, hk, add_mul (b₁.k + 1) 1, one_mul] at e3
  rw [e]
  refine neighbour_fbox_k ?_ ?_
  · generalize (b₁.j + 1) * 2 ^ d = A at *; omega
  · generalize (b₁.k + 1) * 2 ^ d = A at *; omega

lemma rtg_of_isChain {α β : Type*} {r : α → α → Prop} {R : β → β → Prop} (f : α → β) :
    ∀ (l : List α) (a : α), (a :: l).IsChain r →
      (∀ x ∈ a :: l, ∀ y ∈ a :: l, r x y → ReflTransGen R (f x) (f y)) →
      ∀ x ∈ a :: l, ReflTransGen R (f a) (f x)
  | [], a, _, _, x, hx => by
    rw [List.mem_singleton] at hx; subst hx; exact .refl
  | b :: l, a, hch, hR, x, hx => by
    rw [List.isChain_cons_cons] at hch
    have hab := hR a List.mem_cons_self b (List.mem_cons_of_mem _ List.mem_cons_self) hch.1
    rcases List.mem_cons.1 hx with rfl | hx
    · exact .refl
    · exact hab.trans (rtg_of_isChain f l b hch.2 (fun x hx y hy =>
        hR x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) x hx)

lemma mem_of_isChain_ringRel {S : Set DyBox} :
    ∀ (l : List DyBox) (a : DyBox), (a :: l).IsChain (ringRel S) → a ∈ S → ∀ y ∈ a :: l, y ∈ S
  | [], a, _, ha, y, hy => by rw [List.mem_singleton] at hy; subst hy; exact ha
  | b :: l, a, hch, ha, y, hy => by
    rw [List.isChain_cons_cons] at hch
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ha
    · exact mem_of_isChain_ringRel l b hch.2 hch.1.2.1 y hy

/-- **Boundary boxes of an enclosure enclose** (DZZ l. 1393–1397; own elementary argument). -/
theorem hasEnclosure_ring {B : DyBox} {k : ℕ} (d : ℕ) {g : DyBox → Prop}
    (h : HasEnclosure B k fun b' => ∀ bt ∈ boxCollBdry b' d, g bt) :
    HasEnclosure B (k + d) g := by
  obtain ⟨l, hl, hch, hmem, henc⟩ := h
  have hlev : ∀ b ∈ l, b.n = B.n + k := fun b hb => (hmem b hb).1.1
  obtain ⟨b₀, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  set S := ringSet d (b₀ :: l')
  -- corners along the chain
  have hcorner : ∀ x ∈ b₀ :: l', ReflTransGen (ringRel S) (ringCorner d b₀) (ringCorner d x) := by
    refine rtg_of_isChain (ringCorner d) l' b₀ hch fun x hx y hy hxy => ?_
    have hn : y.n = x.n := by rw [hlev x hx, hlev y hy]
    rcases neighbour_idx hn.symm hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact corner_adj_j hx hy hn h1 h2
    · exact ringRel_rtg_symm (corner_adj_j hy hx hn.symm h1 h2.symm)
    · exact corner_adj_k hx hy hn h1 h2
    · exact ringRel_rtg_symm (corner_adj_k hy hx hn.symm h1 h2.symm)
  have hconn : ∀ x ∈ S, ∀ y ∈ S, ReflTransGen (ringRel S) x y := by
    rintro x ⟨b₁, hb₁, hx⟩ y ⟨b₂, hb₂, hy⟩
    exact ((ring_to_corner hb₁ hx).trans (ringRel_rtg_symm (hcorner b₁ hb₁))).trans
      ((hcorner b₂ hb₂).trans (ringRel_rtg_symm (ring_to_corner hb₂ hy)))
  -- finiteness
  set L := B.n + k + d
  have hfin : S.Finite := by
    refine ((Finset.range (2 ^ L) ×ˢ Finset.range (2 ^ L)).image
      (fun q : ℕ × ℕ => fbox L q.1 q.2)).finite_toSet.subset ?_
    rintro bt ⟨b, hb, hr⟩
    have hn : bt.n = L := by rw [hr.1, hlev b hb]
    have e : fbox L bt.j bt.k = bt := by rw [← hn]; exact fbox_self bt
    have hj := bt.hj; have hk := bt.hk
    rw [hn] at hj hk
    simp only [Finset.coe_image, Finset.coe_product, Finset.coe_range, Set.mem_image,
      Set.mem_prod, Set.mem_Iio, Prod.exists]
    exact ⟨bt.j, bt.k, ⟨hj, hk⟩, e⟩
  obtain ⟨L1, hc1, hcov⟩ := exists_isChain_cover hconn hfin.toFinset.toList
    (fun x hx => by simpa using hx) (ringCorner d b₀) (ringCorner_mem List.mem_cons_self)
  have hmemS := mem_of_isChain_ringRel L1 _ hc1 (ringCorner_mem List.mem_cons_self)
  refine ⟨ringCorner d b₀ :: L1, by simp, hc1.imp fun a b h => h.2.2, ?_, ?_⟩
  · intro bt hbt
    obtain ⟨b, hb, hr⟩ := hmemS bt hbt
    have hsub := closedBox_sub_of_ring hr
    refine ⟨⟨by rw [hr.1, hlev b hb, Nat.add_assoc], hsub.trans (hmem b hb).1.2⟩,
      Disjoint.mono_left (interior_mono hsub) (hmem b hb).2.1,
      (hmem b hb).2.2 bt (ring_mem_boxCollBdry hr)⟩
  · intro p hpV hp0 hp1
    obtain ⟨t, b, hb, hpt⟩ := henc p hpV hp0 hp1
    have hfr : ∃ s, p s ∈ frontier b.closedBox := by
      by_cases hint : p t ∈ interior b.closedBox
      · have hA : (frontier (p ⁻¹' interior b.closedBox)).Nonempty := by
          refine nonempty_frontier_iff.2 ⟨⟨t, hint⟩, fun hu => ?_⟩
          have h0 : (0 : unitInterval) ∈ p ⁻¹' interior b.closedBox := hu ▸ mem_univ _
          exact Set.disjoint_left.1 (hmem b hb).2.1 h0 hp0
        obtain ⟨s, hs⟩ := hA
        exact ⟨s, frontier_interior_subset (p.continuous.frontier_preimage_subset _ hs)⟩
      · exact ⟨t, by rw [(isClosed_closedBox b).frontier_eq]; exact ⟨hpt, hint⟩⟩
    obtain ⟨s, hs⟩ := hfr
    obtain ⟨bt, hr, hz⟩ := exists_ring_of_frontier d hs
    exact ⟨s, bt, hcov bt (Finset.mem_toList.2 (hfin.mem_toFinset.2 ⟨b, hb, hr⟩)), hz⟩

end DZZ
end LQGMetric
