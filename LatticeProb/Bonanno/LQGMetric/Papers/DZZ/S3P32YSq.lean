/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32YSq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32XW

/-!
# DZZ P3.2 upper bound at the walled measure: the wall-interior ring squares (D102, P-4aW)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, crossing of Lemma 3.5 (l. 1067–1077)
on the level-`N` grid (decision D84) with the wall-interior boundary squares `ringSqW` of
decision D102 (decisions/DEC-102.md §4(d,e)):

* `hub4`: four sets in cyclic order (consecutive nonempty ones meet, opposite ones not both
  empty) have a common hub for any symmetric transitive relation total on each of them (used for
  the squares here and for the boundary curves in S3P32YGeo);
* `bdryW_iff`: integer description of `IsBdrySqW`;
* `isBdrySqW_of_adj`, **`not_esc_ringW`** (DEC-102 §4(e));
* `bdry_connW`, `bdry_linkW`, **`ringSqW_conn`** (DEC-102 §4(d)).

Own elementary arguments (DV-D84, DV-D102).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-! ### Four sets in cyclic order -/

lemma hub_core {α : Type*} (R : α → α → Prop) (ht : ∀ x y z, R x y → R y z → R x z)
    {A1 A2 A3 A4 : Set α} (c1 : ∀ x ∈ A1, ∀ y ∈ A1, R x y) (c2 : ∀ x ∈ A2, ∀ y ∈ A2, R x y)
    (c3 : ∀ x ∈ A3, ∀ y ∈ A3, R x y) (c4 : ∀ x ∈ A4, ∀ y ∈ A4, R x y) {h : α} (h3 : h ∈ A3)
    (h4 : h ∈ A4) (m1 : A1.Nonempty → (A1 ∩ A4).Nonempty)
    (m2 : A2.Nonempty → (A2 ∩ A3).Nonempty) :
    ∀ x, (x ∈ A1 ∨ x ∈ A2 ∨ x ∈ A3 ∨ x ∈ A4) → R x h := by
  rintro x (hx | hx | hx | hx)
  · obtain ⟨w, hw1, hw4⟩ := m1 ⟨x, hx⟩
    exact ht _ _ _ (c1 x hx w hw1) (c4 w hw4 h h4)
  · obtain ⟨w, hw2, hw3⟩ := m2 ⟨x, hx⟩
    exact ht _ _ _ (c2 x hx w hw2) (c3 w hw3 h h3)
  · exact c3 x hx h h3
  · exact c4 x hx h h4

/-- **A hub for four sets in cyclic order.** -/
lemma hub4 {α : Type*} (R : α → α → Prop) (ht : ∀ x y z, R x y → R y z → R x z)
    {A1 A2 A3 A4 : Set α} (c1 : ∀ x ∈ A1, ∀ y ∈ A1, R x y) (c2 : ∀ x ∈ A2, ∀ y ∈ A2, R x y)
    (c3 : ∀ x ∈ A3, ∀ y ∈ A3, R x y) (c4 : ∀ x ∈ A4, ∀ y ∈ A4, R x y)
    (m12 : A1.Nonempty → A2.Nonempty → (A1 ∩ A2).Nonempty)
    (m23 : A2.Nonempty → A3.Nonempty → (A2 ∩ A3).Nonempty)
    (m34 : A3.Nonempty → A4.Nonempty → (A3 ∩ A4).Nonempty)
    (m41 : A4.Nonempty → A1.Nonempty → (A4 ∩ A1).Nonempty)
    (o13 : A1.Nonempty ∨ A3.Nonempty) (o24 : A2.Nonempty ∨ A4.Nonempty) :
    ∃ h, (h ∈ A1 ∨ h ∈ A2 ∨ h ∈ A3 ∨ h ∈ A4) ∧
      ∀ x, (x ∈ A1 ∨ x ∈ A2 ∨ x ∈ A3 ∨ x ∈ A4) → R x h := by
  have sw : ∀ {X Y : Set α}, (X ∩ Y).Nonempty → (Y ∩ X).Nonempty := fun ⟨w, a, b⟩ => ⟨w, b, a⟩
  by_cases n3 : A3.Nonempty <;> by_cases n4 : A4.Nonempty
  · obtain ⟨h, h3, h4⟩ := m34 n3 n4
    exact ⟨h, Or.inr (Or.inr (Or.inl h3)), hub_core R ht c1 c2 c3 c4 h3 h4
      (fun n1 => sw (m41 n4 n1)) (fun n2 => m23 n2 n3)⟩
  · have n2 := o24.resolve_right n4
    obtain ⟨h, h2, h3⟩ := m23 n2 n3
    exact ⟨h, Or.inr (Or.inl h2), fun x hx => hub_core R ht c4 c1 c2 c3 h2 h3
      (fun n4' => absurd n4' n4) (fun n1 => m12 n1 n2) x (by rcases hx with h' | h' | h' | h' <;> simp [h'])⟩
  · have n1 := o13.resolve_right n3
    obtain ⟨h, h4, h1⟩ := m41 n4 n1
    exact ⟨h, Or.inl h1, fun x hx => hub_core R ht c2 c3 c4 c1 h4 h1
      (fun n2 => sw (m12 n1 n2)) (fun n3' => absurd n3' n3) x (by rcases hx with h' | h' | h' | h' <;> simp [h'])⟩
  · have n1 := o13.resolve_right n3
    have n2 := o24.resolve_right n4
    obtain ⟨h, h1, h2⟩ := m12 n1 n2
    exact ⟨h, Or.inl h1, fun x hx => hub_core R ht c3 c4 c1 c2 h1 h2
      (fun n3' => absurd n3' n3) (fun n4' => absurd n4' n4) x (by rcases hx with h' | h' | h' | h' <;> simp [h'])⟩

/-! ### Integer description of the wall-interior boundary squares -/

lemma two_pow_splitY {n N : ℕ} (h : n ≤ N) : 2 ^ N = 2 ^ n * 2 ^ (N - n) := by
  rw [← pow_add]; congr 1; omega

lemma bdryW_iff {N : ℕ} {B s : DyBox} (hB : B.n ≤ N) (hs : s.n = N) :
    IsBdrySqW N B s ↔
      (B.j * 2 ^ (N - B.n) ≤ s.j ∧ s.j + 1 ≤ B.j * 2 ^ (N - B.n) + 2 ^ (N - B.n) ∧
        B.k * 2 ^ (N - B.n) ≤ s.k ∧ s.k + 1 ≤ B.k * 2 ^ (N - B.n) + 2 ^ (N - B.n)) ∧
      ((s.j = B.j * 2 ^ (N - B.n) ∧ B.j * 2 ^ (N - B.n) ≠ 0) ∨
        (s.j + 1 = B.j * 2 ^ (N - B.n) + 2 ^ (N - B.n) ∧
          B.j * 2 ^ (N - B.n) + 2 ^ (N - B.n) ≠ 2 ^ N) ∨
        (s.k = B.k * 2 ^ (N - B.n) ∧ B.k * 2 ^ (N - B.n) ≠ 0) ∨
        (s.k + 1 = B.k * 2 ^ (N - B.n) + 2 ^ (N - B.n) ∧
          B.k * 2 ^ (N - B.n) + 2 ^ (N - B.n) ≠ 2 ^ N)) := by
  have hM : 0 < 2 ^ (N - B.n) := by positivity
  have e := two_pow_splitY hB
  have w0 : ∀ a : ℕ, a ≠ 0 ↔ a * 2 ^ (N - B.n) ≠ 0 := fun a =>
    ⟨fun h => Nat.mul_ne_zero h hM.ne', fun h e => h (by rw [e, zero_mul])⟩
  have w1 : ∀ a : ℕ, a + 1 ≠ 2 ^ B.n ↔ a * 2 ^ (N - B.n) + 2 ^ (N - B.n) ≠ 2 ^ N := fun a => by
    rw [e, ← add_one_mul]; exact (Nat.mul_left_inj hM.ne').not.symm
  have ea : ∀ a : ℕ, (a + 1) * 2 ^ (N - B.n) = a * 2 ^ (N - B.n) + 2 ^ (N - B.n) :=
    fun a => add_one_mul _ _
  constructor
  · rintro ⟨-, hsub, hc⟩
    obtain ⟨c1, c2, c3, c4⟩ := int_of_sub_closedBox hs hB hsub
    simp only [ea] at c2 c4 hc
    rw [w0 B.j, w0 B.k, w1 B.j, w1 B.k] at hc
    exact ⟨⟨c1, c2, c3, c4⟩, hc⟩
  · rintro ⟨⟨c1, c2, c3, c4⟩, hc⟩
    refine ⟨hs, bx_sub_closedBox hs hB (by exact_mod_cast c1) ?_ (by exact_mod_cast c3) ?_, ?_⟩
    · rw [← ea] at c2; exact_mod_cast c2
    · rw [← ea] at c4; exact_mod_cast c4
    · rw [ea, ea, w0 B.j, w0 B.k, w1 B.j, w1 B.k]; exact hc

/-! ### (e) The reduced ring still encloses -/

/-- A 4-step from a square not in `B` into `B` lands on a wall-interior boundary square. -/
lemma isBdrySqW_of_adj {a b B : DyBox} {N : ℕ} (ha : a.n = N) (hB : B.n ≤ N) (hab : SqAdj a b)
    (haB : ¬ a.closedBox ⊆ B.closedBox) (hbB : b.closedBox ⊆ B.closedBox) : IsBdrySqW N B b := by
  have hb : b.n = N := hab.1 ▸ ha
  have haj : a.j < 2 ^ N := ha ▸ a.hj
  have hak : a.k < 2 ^ N := ha ▸ a.hk
  obtain ⟨c1, c2, c3, c4⟩ := int_of_sub_closedBox hb hB hbB
  have hna : ¬ (B.j * 2 ^ (N - B.n) ≤ a.j ∧ a.j + 1 ≤ (B.j + 1) * 2 ^ (N - B.n) ∧
      B.k * 2 ^ (N - B.n) ≤ a.k ∧ a.k + 1 ≤ (B.k + 1) * 2 ^ (N - B.n)) := by
    rintro ⟨d1, d2, d3, d4⟩
    exact haB (bx_sub_closedBox ha hB (by exact_mod_cast d1) (by exact_mod_cast d2)
      (by exact_mod_cast d3) (by exact_mod_cast d4))
  simp only [add_one_mul] at c2 c4 hna
  rw [bdryW_iff hB hb]
  refine ⟨⟨c1, c2, c3, c4⟩, ?_⟩
  rcases hab.2 with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> omega

/-- **(F1) for the reduced ring** (DEC-102 §4(e)). -/
theorem not_esc_ringW {N : ℕ} {C : DyBox} {U : Set DyBox} (hsep : SqSep N C U)
    (hU : ∀ B ∈ U, B.n ≤ N) (hdisj : ∀ B ∈ U, Disjoint (interior B.closedBox) C.closedBox)
    {s : DyBox} (hs : s.n = N) (hsC : s.closedBox ⊆ C.closedBox) :
    ¬ Esc (ringSqW N U) C.largeBox s := by
  rintro ⟨-, t, hst, ht⟩
  have hfs : SqFree U s := fun B hB hsB => disjoint_left.mp (hdisj B hB)
    (interior_mono hsB (center_mem_interior' s)) (hsC (center_mem_closedBox' s))
  have key : ∀ c, Relation.ReflTransGen (StepAv (ringSqW N U)) s c →
      c.n = N ∧ SqFree U c ∧ Relation.ReflTransGen (SqStep U) s c := by
    intro c hc
    induction hc with
    | refl => exact ⟨hs, hfs, .refl⟩
    | tail _ hbc ih =>
      obtain ⟨hbn, hbf, hb⟩ := ih
      rename_i b c _
      refine ⟨hbc.1.1 ▸ hbn, ?_, ?_⟩
      · intro B hB hcB
        exact hbc.2 ⟨B, hB, isBdrySqW_of_adj hbn (hU B hB) hbc.1 (hbf B hB) hcB⟩
      · refine hb.tail ⟨hbc.1, fun B hB hcB => ?_⟩
        exact hbc.2 ⟨B, hB, isBdrySqW_of_adj hbn (hU B hB) hbc.1 (hbf B hB) hcB⟩
  obtain ⟨-, -, h⟩ := key t hst
  exact ht (hsep s t hs hsC hfs h)

/-! ### (d) The reduced ring is connected -/

/-- The wall-interior boundary squares of `B` at level `N`. -/
def bdrySetW (N : ℕ) (B : DyBox) : Set DyBox := {b | IsBdrySqW N B b}

lemma eq_sqAtY {s : DyBox} {N p q : ℕ} (hs : s.n = N) (hj : s.j = p) (hk : s.k = q)
    (hp : p < 2 ^ N) (hq : q < 2 ^ N) : s = sqAt N p q hp hq := by
  obtain ⟨n, j, k, _, _⟩ := s
  simp only [sqAt, DyBox.mk.injEq] at *
  exact ⟨hs, hj, hk⟩

lemma col_connY {Y : Set DyBox} {N p q q' : ℕ} (hp : p < 2 ^ N) (hq : q < 2 ^ N) (hqq : q ≤ q')
    (hq' : q' < 2 ^ N) (hY : ∀ i (hi : i < 2 ^ N), q ≤ i → i ≤ q' → sqAt N p i hp hi ∈ Y) :
    ConnIn Y (sqAt N p q hp hq) (sqAt N p q' hp hq') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hqq
  exact ⟨hY _ hq le_rfl (by omega), (col_seg hp (· ∈ Y) d q hq hq' fun i hi a b => hY i hi a b).1⟩

lemma row_connY {Y : Set DyBox} {N p p' q : ℕ} (hq : q < 2 ^ N) (hp : p < 2 ^ N) (hpp : p ≤ p')
    (hp' : p' < 2 ^ N) (hY : ∀ i (hi : i < 2 ^ N), p ≤ i → i ≤ p' → sqAt N i q hi hq ∈ Y) :
    ConnIn Y (sqAt N p q hp hq) (sqAt N p' q hp' hq) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpp
  exact ⟨hY _ hp le_rfl (by omega), (row_seg hq (· ∈ Y) d p hp hp' fun i hi a b => hY i hi a b).1⟩

lemma clique_of_base {Y A : Set DyBox} {c : DyBox} (h : ∀ x ∈ A, ConnIn Y x c) :
    ∀ x ∈ A, ∀ y ∈ A, ConnIn Y x y := fun x hx y hy => (h x hx).trans (h y hy).symm

set_option maxHeartbeats 1000000 in
/-- **The wall-interior boundary squares of a box of level `≥ 1` are 4-connected.** -/
lemma bdry_connW {N : ℕ} {B : DyBox} (hB : B.n ≤ N) (hB1 : 1 ≤ B.n) :
    ∀ x ∈ bdrySetW N B, ∀ y ∈ bdrySetW N B, ConnIn (bdrySetW N B) x y := by
  set Y := bdrySetW N B with hYdef
  set M := 2 ^ (N - B.n) with hMdef
  set P := B.j * M with hPdef
  set Q := B.k * M with hQdef
  set S := 2 ^ N with hSdef
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hPS : P + M ≤ S := by have := succ_mul_le_two_pow hB B.hj; rw [add_one_mul] at this; exact this
  have hQS : Q + M ≤ S := by have := succ_mul_le_two_pow hB B.hk; rw [add_one_mul] at this; exact this
  have hMS : M < S := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hP0 : P = 0 → B.j = 0 := fun h => by
    rcases Nat.mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd h (by positivity)
  have hPM : P = 0 → P + M ≠ S := fun h => by omega
  have hQM : Q = 0 → Q + M ≠ S := fun h => by omega
  -- membership in `Y` from integer data
  have memY : ∀ i q (hi : i < S) (hq : q < S), P ≤ i → i + 1 ≤ P + M → Q ≤ q → q + 1 ≤ Q + M →
      ((i = P ∧ P ≠ 0) ∨ (i + 1 = P + M ∧ P + M ≠ S) ∨ (q = Q ∧ Q ≠ 0) ∨
        (q + 1 = Q + M ∧ Q + M ≠ S)) → sqAt N i q hi hq ∈ Y := by
    intro i q hi hq a b c d h
    exact (bdryW_iff hB rfl).2 ⟨⟨a, b, c, d⟩, h⟩
  have intY : ∀ s ∈ Y, s.n = N ∧ (P ≤ s.j ∧ s.j + 1 ≤ P + M ∧ Q ≤ s.k ∧ s.k + 1 ≤ Q + M) ∧
      ((s.j = P ∧ P ≠ 0) ∨ (s.j + 1 = P + M ∧ P + M ≠ S) ∨ (s.k = Q ∧ Q ≠ 0) ∨
        (s.k + 1 = Q + M ∧ Q + M ≠ S)) := by
    intro s hs
    have hsn : s.n = N := hs.1
    exact ⟨hsn, (bdryW_iff hB hsn).1 hs⟩
  have hPl : P < S := by omega
  have hQl : Q < S := by omega
  have hPr : P + M - 1 < S := by omega
  have hQr : Q + M - 1 < S := by omega
  set A1 : Set DyBox := {s | s ∈ Y ∧ s.j = P ∧ P ≠ 0}
  set A2 : Set DyBox := {s | s ∈ Y ∧ s.k = Q ∧ Q ≠ 0}
  set A3 : Set DyBox := {s | s ∈ Y ∧ s.j + 1 = P + M ∧ P + M ≠ S}
  set A4 : Set DyBox := {s | s ∈ Y ∧ s.k + 1 = Q + M ∧ Q + M ≠ S}
  have c1 : ∀ x ∈ A1, ∀ y ∈ A1, ConnIn Y x y := clique_of_base (c := sqAt N P Q hPl hQl) <| by
    rintro s ⟨hs, hj, hP⟩
    obtain ⟨hsn, ⟨a, b, c, d⟩, -⟩ := intY s hs
    rw [eq_sqAtY hsn hj rfl hPl (by omega)]
    exact (col_connY hPl hQl c (by omega) fun i hi a' b' =>
      memY _ _ _ _ le_rfl (by omega) a' (by omega) (Or.inl ⟨rfl, hP⟩)).symm
  have c2 : ∀ x ∈ A2, ∀ y ∈ A2, ConnIn Y x y := clique_of_base (c := sqAt N P Q hPl hQl) <| by
    rintro s ⟨hs, hk, hQ⟩
    obtain ⟨hsn, ⟨a, b, c, d⟩, -⟩ := intY s hs
    rw [eq_sqAtY hsn rfl hk (by omega) hQl]
    exact (row_connY hQl hPl a (by omega) fun i hi a' b' =>
      memY _ _ _ _ a' (by omega) le_rfl (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl, hQ⟩)))).symm
  have c3 : ∀ x ∈ A3, ∀ y ∈ A3, ConnIn Y x y := clique_of_base (c := sqAt N (P + M - 1) Q hPr hQl) <| by
    rintro s ⟨hs, hj, hP⟩
    obtain ⟨hsn, ⟨a, b, c, d⟩, -⟩ := intY s hs
    rw [eq_sqAtY hsn (show s.j = P + M - 1 by omega) rfl hPr (by omega)]
    exact (col_connY hPr hQl c (by omega) fun i hi a' b' =>
      memY _ _ _ _ (by omega) (by omega) a' (by omega) (Or.inr (Or.inl ⟨by omega, hP⟩))).symm
  have c4 : ∀ x ∈ A4, ∀ y ∈ A4, ConnIn Y x y := clique_of_base (c := sqAt N P (Q + M - 1) hPl hQr) <| by
    rintro s ⟨hs, hk, hQ⟩
    obtain ⟨hsn, ⟨a, b, c, d⟩, -⟩ := intY s hs
    rw [eq_sqAtY hsn rfl (show s.k = Q + M - 1 by omega) (by omega) hQr]
    exact (row_connY hQr hPl a (by omega) fun i hi a' b' =>
      memY _ _ _ _ a' (by omega) (by omega) (by omega)
        (Or.inr (Or.inr (Or.inr ⟨by omega, hQ⟩)))).symm
  have cover : ∀ s ∈ Y, s ∈ A1 ∨ s ∈ A2 ∨ s ∈ A3 ∨ s ∈ A4 := by
    intro s hs
    obtain ⟨-, -, h | h | h | h⟩ := intY s hs
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hs, h⟩))
    · exact Or.inr (Or.inl ⟨hs, h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hs, h⟩))
  obtain ⟨h, -, hh⟩ := hub4 (ConnIn Y) (fun _ _ _ a b => a.trans b) c1 c2 c3 c4
    (fun ⟨_, _, _, h1⟩ ⟨_, _, _, h2⟩ => ⟨sqAt N P Q hPl hQl,
      ⟨memY _ _ _ _ le_rfl (by omega) le_rfl (by omega) (Or.inl ⟨rfl, h1⟩), rfl, h1⟩,
      ⟨memY _ _ _ _ le_rfl (by omega) le_rfl (by omega) (Or.inl ⟨rfl, h1⟩), rfl, h2⟩⟩)
    (fun ⟨_, _, _, h1⟩ ⟨_, _, _, h2⟩ => ⟨sqAt N (P + M - 1) Q hPr hQl,
      ⟨memY _ _ _ _ (by omega) (by omega) le_rfl (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩))),
        rfl, h1⟩,
      ⟨memY _ _ _ _ (by omega) (by omega) le_rfl (by omega) (Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩))),
        (by simp only [sqAt]; omega), h2⟩⟩)
    (fun ⟨_, _, _, h1⟩ ⟨_, _, _, h2⟩ => ⟨sqAt N (P + M - 1) (Q + M - 1) hPr hQr,
      ⟨memY _ _ _ _ (by omega) (by omega) (by omega) (by omega)
        (Or.inr (Or.inl ⟨by omega, h1⟩)), (by simp only [sqAt]; omega), h1⟩,
      ⟨memY _ _ _ _ (by omega) (by omega) (by omega) (by omega)
        (Or.inr (Or.inl ⟨by omega, h1⟩)), (by simp only [sqAt]; omega), h2⟩⟩)
    (fun ⟨_, _, _, h1⟩ ⟨_, _, _, h2⟩ => ⟨sqAt N P (Q + M - 1) hPl hQr,
      ⟨memY _ _ _ _ le_rfl (by omega) (by omega) (by omega) (Or.inl ⟨rfl, h2⟩),
        (by simp only [sqAt]; omega), h1⟩,
      ⟨memY _ _ _ _ le_rfl (by omega) (by omega) (by omega) (Or.inl ⟨rfl, h2⟩), rfl, h2⟩⟩)
    (by
      by_cases h0 : P = 0
      · exact Or.inr ⟨sqAt N (P + M - 1) Q hPr hQl, memY _ _ _ _ (by omega) (by omega) le_rfl
          (by omega) (Or.inr (Or.inl ⟨by omega, hPM h0⟩)), (by simp only [sqAt]; omega), hPM h0⟩
      · exact Or.inl ⟨sqAt N P Q hPl hQl, memY _ _ _ _ le_rfl (by omega) le_rfl (by omega)
          (Or.inl ⟨rfl, h0⟩), rfl, h0⟩)
    (by
      by_cases h0 : Q = 0
      · exact Or.inr ⟨sqAt N P (Q + M - 1) hPl hQr, memY _ _ _ _ le_rfl (by omega) (by omega)
          (by omega) (Or.inr (Or.inr (Or.inr ⟨by omega, hQM h0⟩))), (by simp only [sqAt]; omega),
          hQM h0⟩
      · exact Or.inl ⟨sqAt N P Q hPl hQl, memY _ _ _ _ le_rfl (by omega) le_rfl (by omega)
          (Or.inr (Or.inr (Or.inl ⟨rfl, h0⟩))), rfl, h0⟩)
  exact fun x hx y hy => (hh x (cover x hx)).trans (hh y (cover y hy)).symm

/-- Neighbouring boxes of one level have 4-adjacent wall-interior boundary squares. -/
lemma bdry_linkW {B₁ B₂ : DyBox} {N : ℕ} (hn : B₁.n = B₂.n) (h1 : B₁.n ≤ N)
    (h : Neighbour B₁ B₂) : ∃ x ∈ bdrySetW N B₁, ∃ y ∈ bdrySetW N B₂, SqAdj x y := by
  have h2 : B₂.n ≤ N := hn ▸ h1
  obtain ⟨x, y, hxn, hx, hy, hxy⟩ := exists_sqAdj_of_neighbour'
    (eq_of_sub_same_level hn h1) (eq_of_sub_same_level hn.symm h2) h1 h2 h
  have hyn : y.n = N := hxy.1 ▸ hxn
  have hyB₁ : ¬ y.closedBox ⊆ B₁.closedBox := fun hy1 =>
    h.1 ((anc_eq_of_sub hyn h1 hy1).symm.trans (by rw [hn]; exact anc_eq_of_sub hyn h2 hy))
  have hxB₂ : ¬ x.closedBox ⊆ B₂.closedBox := fun hx2 =>
    h.1 ((anc_eq_of_sub hxn h1 hx).symm.trans (by rw [hn]; exact anc_eq_of_sub hxn h2 hx2))
  exact ⟨x, isBdrySqW_of_adj hyn h1 hxy.symm hyB₁ hx, y, isBdrySqW_of_adj hxn h2 hxy hxB₂ hy, hxy⟩

/-- **The reduced ring of a `Neighbour`-chain of boxes of one level is 4-connected**
(DEC-102 §4(d)). -/
theorem ringSqW_conn {N : ℕ} : ∀ l : List DyBox, l.IsChain Neighbour → (∀ b ∈ l, b.n ≤ N) →
    (∀ b ∈ l, 1 ≤ b.n) → (∀ b ∈ l, ∀ b' ∈ l, b.n = b'.n) →
    ∀ x ∈ ringSqW N {b | b ∈ l}, ∀ y ∈ ringSqW N {b | b ∈ l}, ConnIn (ringSqW N {b | b ∈ l}) x y
  | [], _, _, _, _, x, hx, _, _ => by obtain ⟨B, hB, -⟩ := hx; simp at hB
  | [b], _, hN, h1, _, x, hx, y, hy => by
    have sub : bdrySetW N b ⊆ ringSqW N {b' | b' ∈ [b]} := fun z hz => ⟨b, by simp, hz⟩
    obtain ⟨B, hB, hxB⟩ := hx
    obtain ⟨B', hB', hyB⟩ := hy
    simp only [List.mem_singleton, mem_ofPred_eq] at hB hB'
    subst hB hB'
    exact (bdry_connW (hN _ (by simp)) (h1 _ (by simp)) x hxB y hyB).mono sub
  | b :: c :: t, hch, hN, h1, hlev, x, hx, y, hy => by
    rw [List.isChain_cons_cons] at hch
    set Y := ringSqW N {b' | b' ∈ b :: c :: t}
    have subb : bdrySetW N b ⊆ Y := fun z hz => ⟨b, by simp, hz⟩
    have subt : ringSqW N {b' | b' ∈ c :: t} ⊆ Y := fun z ⟨B, hB, hz⟩ =>
      ⟨B, List.mem_cons_of_mem _ hB, hz⟩
    have ih := ringSqW_conn (c :: t) hch.2 (fun b' hb' => hN b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' => h1 b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' b'' hb'' => hlev b' (List.mem_cons_of_mem _ hb') b'' (List.mem_cons_of_mem _ hb''))
    obtain ⟨x0, hx0, y0, hy0, hxy0⟩ := bdry_linkW (hlev b (by simp) c (by simp)) (hN b (by simp))
      hch.1
    have hy0t : y0 ∈ ringSqW N {b' | b' ∈ c :: t} := ⟨c, by simp, hy0⟩
    have hto : ∀ z ∈ Y, ConnIn Y x0 z := by
      rintro z ⟨B, hB, hz⟩
      simp only [mem_ofPred_eq, List.mem_cons] at hB
      rcases hB with rfl | hB
      · exact (bdry_connW (hN B (by simp)) (h1 B (by simp)) x0 hx0 z hz).mono subb
      · have hzt : z ∈ ringSqW N {b' | b' ∈ c :: t} := ⟨B, by
          simp only [mem_ofPred_eq, List.mem_cons]; exact hB, hz⟩
        exact ConnIn.trans (y := y0) ⟨subb hx0, .single ⟨hxy0, subt hy0t⟩⟩
          ((ih y0 hy0t z hzt).mono subt)
    exact (hto x hx).symm.trans (hto y hy)

end DZZ
end LQGMetric
