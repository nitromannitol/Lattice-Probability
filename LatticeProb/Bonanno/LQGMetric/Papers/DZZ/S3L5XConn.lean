/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XConn at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XGeo

/-!
# DZZ Lemma 3.5: the ring of an enclosure is 4-connected (P2-DEC84, D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1067–1071): DZZ's `ℂ_i` is "a
sequence of neighboring cells"; on the level-`N` grid (decision D84) the ring `ringSq N U` of the
boundary squares of a chain of neighbouring boxes is 4-connected (input `hconn` of
`l35_recursion`).

* `bdry_conn_corner`: every boundary square of a box is joined to its corner square along the
  boundary.
* **`ringSq_conn`**: the ring of a `Neighbour`-chain of boxes of one level is 4-connected.

Own elementary arguments; DEVIATIONS DV-D84. (P2-DZZ316 builds the same ring structure for
DZZ Lemma 3.16 in S3L316P2/P3, not yet committed; the two can be merged later.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- The boundary squares of `B` at level `N`. -/
def bdrySet (N : ℕ) (B : DyBox) : Set DyBox := {b | IsBdrySq N B b}

lemma mem_bdrySet {N : ℕ} {B : DyBox} (hB : B.n ≤ N) {i q : ℕ} (hi : i < 2 ^ N) (hq : q < 2 ^ N)
    (h1 : B.j * 2 ^ (N - B.n) ≤ i) (h2 : i + 1 ≤ (B.j + 1) * 2 ^ (N - B.n))
    (h3 : B.k * 2 ^ (N - B.n) ≤ q) (h4 : q + 1 ≤ (B.k + 1) * 2 ^ (N - B.n))
    (hc : i = B.j * 2 ^ (N - B.n) ∨ i + 1 = (B.j + 1) * 2 ^ (N - B.n) ∨
      q = B.k * 2 ^ (N - B.n) ∨ q + 1 = (B.k + 1) * 2 ^ (N - B.n)) :
    sqAt N i q hi hq ∈ bdrySet N B :=
  ⟨rfl, sq_sub_of_bounds hB hi hq h1 h2 h3 h4, hc⟩

lemma bdry_conn_corner {N : ℕ} {B : DyBox} (hB : B.n ≤ N) :
    ∀ s ∈ bdrySet N B, ConnIn (bdrySet N B) (cornerSq N B hB) s := by
  intro s ⟨hsn, hsB, hc⟩
  obtain ⟨s1, s2, s3, s4⟩ := int_of_sub_closedBox hsn hB hsB
  have hw1 : 1 ≤ 2 ^ (N - B.n) := Nat.one_le_two_pow
  have hJ : B.j * 2 ^ (N - B.n) + 1 ≤ (B.j + 1) * 2 ^ (N - B.n) := by nlinarith
  have hK : B.k * 2 ^ (N - B.n) + 1 ≤ (B.k + 1) * 2 ^ (N - B.n) := by nlinarith
  have bj := succ_mul_le_two_pow hB B.hj
  have bk := succ_mul_le_two_pow hB B.hk
  set Y := bdrySet N B
  have ha0 : B.j * 2 ^ (N - B.n) < 2 ^ N := by omega
  have hb0 : B.k * 2 ^ (N - B.n) < 2 ^ N := by omega
  have hsj : s.j < 2 ^ N := hsn ▸ s.hj
  have hsk : s.k < 2 ^ N := hsn ▸ s.hk
  have es := sqAt_eq hsn
  have hcorner : cornerSq N B hB = sqAt N (B.j * 2 ^ (N - B.n)) (B.k * 2 ^ (N - B.n)) ha0 hb0 := rfl
  have hcY : cornerSq N B hB ∈ Y := by
    rw [hcorner]; exact mem_bdrySet hB ha0 hb0 le_rfl (by omega) le_rfl (by omega) (Or.inl rfl)
  -- bottom row from the corner to column `i`
  have bot : ∀ i (hi : i < 2 ^ N), B.j * 2 ^ (N - B.n) ≤ i → i + 1 ≤ (B.j + 1) * 2 ^ (N - B.n) →
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ b ∈ Y) (sqAt N (B.j * 2 ^ (N - B.n)) (B.k * 2 ^ (N - B.n)) ha0 hb0)
        (sqAt N i (B.k * 2 ^ (N - B.n)) hi hb0) := by
    intro i hi h1 h2
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
    exact (row_seg hb0 (· ∈ Y) d (B.j * 2 ^ (N - B.n)) ha0 hi fun i' hi' a b =>
      mem_bdrySet hB hi' hb0 a (by omega) le_rfl (by omega) (Or.inr (Or.inr (Or.inl rfl)))).1
  -- left column from the corner to row `q`
  have lft : ∀ q (hq : q < 2 ^ N), B.k * 2 ^ (N - B.n) ≤ q → q + 1 ≤ (B.k + 1) * 2 ^ (N - B.n) →
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ b ∈ Y) (sqAt N (B.j * 2 ^ (N - B.n)) (B.k * 2 ^ (N - B.n)) ha0 hb0)
        (sqAt N (B.j * 2 ^ (N - B.n)) q ha0 hq) := by
    intro q hq h1 h2
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
    exact (col_seg ha0 (· ∈ Y) d (B.k * 2 ^ (N - B.n)) hb0 hq fun i' hi' a b =>
      mem_bdrySet hB ha0 hi' le_rfl (by omega) a (by omega) (Or.inl rfl)).1
  refine ⟨hcY, ?_⟩
  rw [hcorner, es]
  rcases hc with h | h | h | h
  · -- left column
    have := lft s.k hsk s3 s4
    convert this using 2
  · -- right column: bottom row, then up
    have ha1 : (B.j + 1) * 2 ^ (N - B.n) - 1 < 2 ^ N := by omega
    have r1 := bot ((B.j + 1) * 2 ^ (N - B.n) - 1) ha1 (by omega) (by omega)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le s3
    have r2 := (col_seg ha1 (· ∈ Y) d (B.k * 2 ^ (N - B.n)) hb0 (by omega) fun i' hi' a b =>
      mem_bdrySet hB ha1 hi' (by omega) (by omega) a (by omega)
        (Or.inr (Or.inl (by omega)))).1
    have e : sqAt N s.j s.k hsj hsk = sqAt N ((B.j + 1) * 2 ^ (N - B.n) - 1) (B.k * 2 ^ (N - B.n) + d) ha1 (by omega) := by
      simp only [sqAt, DyBox.mk.injEq, true_and]; omega
    rw [e]; exact r1.trans r2
  · -- bottom row
    have := bot s.j hsj s1 s2
    convert this using 2
  · -- top row: left column, then right
    have hb1 : (B.k + 1) * 2 ^ (N - B.n) - 1 < 2 ^ N := by omega
    have r1 := lft ((B.k + 1) * 2 ^ (N - B.n) - 1) hb1 (by omega) (by omega)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le s1
    have r2 := (row_seg hb1 (· ∈ Y) d (B.j * 2 ^ (N - B.n)) ha0 (by omega) fun i' hi' a b =>
      mem_bdrySet hB hi' hb1 a (by omega) (by omega) (by omega)
        (Or.inr (Or.inr (Or.inr (by omega))))).1
    have e : sqAt N s.j s.k hsj hsk = sqAt N (B.j * 2 ^ (N - B.n) + d) ((B.k + 1) * 2 ^ (N - B.n) - 1) (by omega) hb1 := by
      simp only [sqAt, DyBox.mk.injEq, true_and]; omega
    rw [e]; exact r1.trans r2

lemma bdry_conn {N : ℕ} {B : DyBox} (hB : B.n ≤ N) :
    ∀ x ∈ bdrySet N B, ∀ y ∈ bdrySet N B, ConnIn (bdrySet N B) x y := fun x hx y hy =>
  (bdry_conn_corner hB x hx).symm.trans (bdry_conn_corner hB y hy)

lemma eq_of_sub_same_level {B₁ B₂ : DyBox} {N : ℕ} (hn : B₁.n = B₂.n) (h1 : B₁.n ≤ N)
    (h : B₁.closedBox ⊆ B₂.closedBox) : B₁ = B₂ := by
  have hs := cornerSq_sub B₁ h1
  have e1 := anc_eq_of_sub (s := cornerSq N B₁ h1) rfl h1 hs
  have e2 := anc_eq_of_sub (s := cornerSq N B₁ h1) rfl (hn ▸ h1) (hs.trans h)
  rw [hn] at e1
  exact e1.symm.trans e2

/-- Neighbouring boxes of one level have 4-adjacent boundary squares. -/
lemma bdry_link {B₁ B₂ : DyBox} {N : ℕ} (hn : B₁.n = B₂.n) (h1 : B₁.n ≤ N)
    (h : Neighbour B₁ B₂) : ∃ x ∈ bdrySet N B₁, ∃ y ∈ bdrySet N B₂, SqAdj x y := by
  have h2 : B₂.n ≤ N := hn ▸ h1
  obtain ⟨x, y, hxn, hx, hy, hxy⟩ := exists_sqAdj_of_neighbour'
    (eq_of_sub_same_level hn h1) (eq_of_sub_same_level hn.symm h2) h1 h2 h
  have hyn : y.n = N := hxy.1 ▸ hxn
  have hyB₁ : ¬ y.closedBox ⊆ B₁.closedBox := fun hy1 =>
    h.1 ((anc_eq_of_sub hyn h1 hy1).symm.trans (by rw [hn]; exact anc_eq_of_sub hyn h2 hy))
  have hxB₂ : ¬ x.closedBox ⊆ B₂.closedBox := fun hx2 =>
    h.1 ((anc_eq_of_sub hxn h1 hx).symm.trans (by rw [hn]; exact anc_eq_of_sub hxn h2 hx2))
  exact ⟨x, isBdrySq_of_adj hyn h1 hxy.symm hyB₁ hx, y, isBdrySq_of_adj hxn h2 hxy hxB₂ hy, hxy⟩

/-- **The ring of a `Neighbour`-chain of boxes of one level is 4-connected.** -/
theorem ringSq_conn {N : ℕ} : ∀ l : List DyBox, l.IsChain Neighbour → (∀ b ∈ l, b.n ≤ N) →
    (∀ b ∈ l, ∀ b' ∈ l, b.n = b'.n) →
    ∀ x ∈ ringSq N {b | b ∈ l}, ∀ y ∈ ringSq N {b | b ∈ l}, ConnIn (ringSq N {b | b ∈ l}) x y
  | [], _, _, _, x, hx, _, _ => by obtain ⟨B, hB, -⟩ := hx; simp at hB
  | [b], _, hN, _, x, hx, y, hy => by
    have sub : bdrySet N b ⊆ ringSq N {b' | b' ∈ [b]} := fun z hz => ⟨b, by simp, hz⟩
    obtain ⟨B, hB, hxB⟩ := hx
    obtain ⟨B', hB', hyB⟩ := hy
    simp only [List.mem_singleton, mem_ofPred_eq] at hB hB'
    subst hB hB'
    exact (bdry_conn (hN _ (by simp)) x hxB y hyB).mono sub
  | b :: c :: t, hch, hN, hlev, x, hx, y, hy => by
    rw [List.isChain_cons_cons] at hch
    set Y := ringSq N {b' | b' ∈ b :: c :: t}
    have subb : bdrySet N b ⊆ Y := fun z hz => ⟨b, by simp, hz⟩
    have subt : ringSq N {b' | b' ∈ c :: t} ⊆ Y := fun z ⟨B, hB, hz⟩ =>
      ⟨B, List.mem_cons_of_mem _ hB, hz⟩
    have ih := ringSq_conn (c :: t) hch.2 (fun b' hb' => hN b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' b'' hb'' => hlev b' (List.mem_cons_of_mem _ hb') b'' (List.mem_cons_of_mem _ hb''))
    obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := bdry_link (hlev b (by simp) c (by simp)) (hN b (by simp))
      hch.1
    have hy0t : y0 ∈ ringSq N {b' | b' ∈ c :: t} := ⟨c, by simp, hy0⟩
    have hto : ∀ z ∈ Y, ConnIn Y x0 z := by
      rintro z ⟨B, hB, hz⟩
      simp only [mem_ofPred_eq, List.mem_cons] at hB
      rcases hB with rfl | hB
      · exact (bdry_conn (hN B (by simp)) x0 hx0 z hz).mono subb
      · have hzt : z ∈ ringSq N {b' | b' ∈ c :: t} := ⟨B, by
          simp only [mem_ofPred_eq, List.mem_cons]; exact hB, hz⟩
        exact ConnIn.trans (y := y0) ⟨subb hx0, .single ⟨hxy0, subt hy0t⟩⟩
          ((ih y0 hy0t z hzt).mono subt)
    exact (hto x hx).symm.trans (hto y hy)

end DZZ
end LQGMetric
