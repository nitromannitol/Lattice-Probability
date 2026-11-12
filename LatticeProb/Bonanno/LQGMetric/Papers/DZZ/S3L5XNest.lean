/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XNest at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XBridge

/-!
# DZZ Lemma 3.5: nesting of enclosed regions on the square grid (P2-DEC84, D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1071–1079): the `i_r` recursion
uses, without comment, that regions enclosed by the enclosures of the cells nest. On the level-`N`
square grid (decision D84, DEC-84 §4):

* `StepAv X`: a 4-step into a square not in the wall `X`; `Esc X Λ s`: from `s ∉ X` a 4-path
  avoiding `X` reaches a square not contained in `Λ` (`¬ Esc` = "`s` is enclosed").
* `not_esc_of_reach` (F2): enclosedness propagates along paths avoiding the wall.
* `exists_out_path`: from a square outside `𝖢₂,large` one reaches, through squares outside
  `𝖢₂,large`, a square outside `𝖢₁,large` (`n_{𝖢₁} ≥ 1`: `𝖢₁,large` spans neither the width nor the
  height of `𝕍`).
* **`not_esc_nest`** (F4, the Jordan-type step): if every square of `Y` is enclosed by the wall
  `X` in `𝖢₂,large` and `a` is enclosed by `Y` in `𝖢₁,large`, then `a` is enclosed by `X` in
  `𝖢₂,large`.

Own elementary arguments (DZZ use the nesting implicitly); DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- A 4-step into a square outside the wall `X`. -/
def StepAv (X : Set DyBox) (a b : DyBox) : Prop := SqAdj a b ∧ b ∉ X

/-- From `s ∉ X`, a 4-path avoiding `X` reaches a square not contained in `Λ`. -/
def Esc (X : Set DyBox) (Λ : Set ℂ) (s : DyBox) : Prop :=
  s ∉ X ∧ ∃ t, Relation.ReflTransGen (StepAv X) s t ∧ ¬ t.closedBox ⊆ Λ

/-- (F2) Enclosedness propagates along 4-paths avoiding the wall. -/
lemma not_esc_of_reach {X : Set DyBox} {Λ : Set ℂ} {s t : DyBox}
    (h : Relation.ReflTransGen (StepAv X) s t) (hs : s ∉ X) (hns : ¬ Esc X Λ s) :
    ¬ Esc X Λ t := by
  rintro ⟨-, u, htu, hu⟩
  exact hns ⟨hs, u, h.trans htu, hu⟩

lemma reach_n {P : DyBox → DyBox → Prop} (hP : ∀ a b, P a b → SqAdj a b) {s t : DyBox}
    (h : Relation.ReflTransGen P s t) : t.n = s.n := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ((hP _ _ hbc).1.symm).trans ih

/-- A square not enclosed escapes; squares of `Λ`-enclosed regions lie in `Λ`. -/
lemma sub_of_not_esc {X : Set DyBox} {Λ : Set ℂ} {s : DyBox} (hs : s ∉ X) (h : ¬ Esc X Λ s) :
    s.closedBox ⊆ Λ := by
  by_contra h'
  exact h ⟨hs, s, .refl, h'⟩

/-! ### Squares outside a large box -/

/-- The level-`N` square with indices `(p, q)`. -/
def sqAt (N p q : ℕ) (hp : p < 2 ^ N) (hq : q < 2 ^ N) : DyBox := ⟨N, p, q, hp, hq⟩

lemma sqAt_eq {t : DyBox} {N : ℕ} (ht : t.n = N) :
    t = sqAt N t.j t.k (ht ▸ t.hj) (ht ▸ t.hk) := by
  cases t; cases ht; rfl

/-- Integer bounds of a square contained in `C_large` (evaluation at two corners). -/
lemma int_of_sub_largeBox {C s : DyBox} {N : ℕ} (hs : s.n = N) (hC : C.n + 1 ≤ N)
    (h : s.closedBox ⊆ C.largeBox) :
    (2 * C.j - 1 : ℤ) * 2 ^ (N - C.n - 1) ≤ s.j ∧ (s.j : ℤ) + 1 ≤ (2 * C.j + 3) * 2 ^ (N - C.n - 1) ∧
      (2 * C.k - 1 : ℤ) * 2 ^ (N - C.n - 1) ≤ s.k ∧
      (s.k : ℤ) + 1 ≤ (2 * C.k + 3) * 2 ^ (N - C.n - 1) := by
  have e := bx_side_mul (b := s) (N := N) hs.le
  rw [hs, Nat.sub_self, pow_zero] at e
  have hs0 : 0 < s.side := by unfold DyBox.side; positivity
  have lo : (⟨s.j * s.side, s.k * s.side⟩ : ℂ) ∈ s.closedBox := by
    simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨le_rfl, ?_, le_rfl, ?_⟩ <;> nlinarith
  have hi : (⟨(s.j + 1) * s.side, (s.k + 1) * s.side⟩ : ℂ) ∈ s.closedBox := by
    simp only [DyBox.closedBox, mem_ofPred_eq]; refine ⟨?_, le_rfl, ?_, le_rfl⟩ <;> nlinarith
  obtain ⟨a1, -, a3, -⟩ := (bx_mem_largeBox hC).1 (h lo)
  obtain ⟨-, b2, -, b4⟩ := (bx_mem_largeBox hC).1 (h hi)
  simp only [mul_assoc, e, mul_one] at a1 a3 b2 b4
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast a1
  · exact_mod_cast b2
  · exact_mod_cast a3
  · exact_mod_cast b4

/-- `C_large` (`n_C ≥ 1`) does not span the level-`N` grid. -/
lemma largeBox_not_span {C : DyBox} {N : ℕ} (h1 : 1 ≤ C.n) (hC : C.n + 1 ≤ N) (i : ℕ) :
    ¬ ((2 * i - 1 : ℤ) * 2 ^ (N - C.n - 1) ≤ 0 ∧ (2 : ℤ) ^ N ≤ (2 * i + 3) * 2 ^ (N - C.n - 1)) := by
  rintro ⟨a, b⟩
  have hv : (0 : ℤ) < 2 ^ (N - C.n - 1) := by positivity
  have hi : (i : ℤ) = 0 := by
    by_contra h
    have : (1 : ℤ) ≤ 2 * i - 1 := by omega
    nlinarith
  rw [hi] at b
  have e : (2 : ℤ) ^ N = 2 ^ (C.n + 1) * 2 ^ (N - C.n - 1) := by
    rw [← pow_add]; congr 1; omega
  have h4 : (4 : ℤ) ≤ 2 ^ (C.n + 1) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (C.n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

/-- Vertical 4-paths in a column all of whose squares satisfy `P`. -/
lemma col_path {N p : ℕ} (hp : p < 2 ^ N) (P : DyBox → Prop)
    (hP : ∀ q (hq : q < 2 ^ N), P (sqAt N p q hp hq)) (q₁ q₂ : ℕ) (h₁ : q₁ < 2 ^ N)
    (h₂ : q₂ < 2 ^ N) :
    Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N p q₁ hp h₁) (sqAt N p q₂ hp h₂) := by
  have up : ∀ q d (hq : q < 2 ^ N) (hd : q + d < 2 ^ N),
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N p q hp hq)
        (sqAt N p (q + d) hp hd) := by
    intro q d
    induction d with
    | zero => intro hq hd; exact .refl
    | succ d ih =>
      intro hq hd
      exact (ih hq (by omega)).tail ⟨⟨rfl, Or.inl ⟨rfl, Or.inl (by simp [sqAt]; omega)⟩⟩, hP _ _⟩
  have down : ∀ q d (hq : q < 2 ^ N) (hd : q + d < 2 ^ N),
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N p (q + d) hp hd)
        (sqAt N p q hp hq) := by
    intro q d
    induction d with
    | zero => intro hq hd; exact .refl
    | succ d ih =>
      intro hq hd
      exact Relation.ReflTransGen.head (b := sqAt N p (q + d) hp (by omega))
        ⟨⟨rfl, Or.inl ⟨rfl, Or.inr (by simp [sqAt]; omega)⟩⟩, hP _ _⟩ (ih hq (by omega))
  rcases le_total q₁ q₂ with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact up q₁ d h₁ h₂
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact down q₂ d h₂ h₁

/-- Horizontal 4-paths in a row all of whose squares satisfy `P`. -/
lemma row_path {N q : ℕ} (hq : q < 2 ^ N) (P : DyBox → Prop)
    (hP : ∀ p (hp : p < 2 ^ N), P (sqAt N p q hp hq)) (p₁ p₂ : ℕ) (h₁ : p₁ < 2 ^ N)
    (h₂ : p₂ < 2 ^ N) :
    Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N p₁ q h₁ hq) (sqAt N p₂ q h₂ hq) := by
  have up : ∀ p d (hp : p < 2 ^ N) (hd : p + d < 2 ^ N),
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N p q hp hq)
        (sqAt N (p + d) q hd hq) := by
    intro p d
    induction d with
    | zero => intro hp hd; exact .refl
    | succ d ih =>
      intro hp hd
      exact (ih hp (by omega)).tail ⟨⟨rfl, Or.inr ⟨rfl, Or.inl (by simp [sqAt]; omega)⟩⟩, hP _ _⟩
  have down : ∀ p d (hp : p < 2 ^ N) (hd : p + d < 2 ^ N),
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N (p + d) q hd hq)
        (sqAt N p q hp hq) := by
    intro p d
    induction d with
    | zero => intro hp hd; exact .refl
    | succ d ih =>
      intro hp hd
      exact Relation.ReflTransGen.head (b := sqAt N (p + d) q (by omega) hq)
        ⟨⟨rfl, Or.inr ⟨rfl, Or.inr (by simp [sqAt]; omega)⟩⟩, hP _ _⟩ (ih hp (by omega))
  rcases le_total p₁ p₂ with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact up p₁ d h₁ h₂
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact down p₂ d h₂ h₁

lemma two_pow_sub_one_cast (N : ℕ) : (((2 ^ N - 1 : ℕ) : ℤ) + 1) = 2 ^ N := by
  have : 1 ≤ 2 ^ N := Nat.one_le_two_pow
  push_cast [Nat.cast_sub this]; ring

/-- From a square outside `𝖢₂,large`, a 4-path through squares outside `𝖢₂,large` reaches a square
outside `𝖢₁,large` (`n_{𝖢₁} ≥ 1`). -/
lemma exists_out_path {C₁ C₂ t : DyBox} {N : ℕ} (h1 : 1 ≤ C₁.n) (hN1 : C₁.n + 1 ≤ N)
    (hN2 : C₂.n + 1 ≤ N) (ht : t.n = N) (hout : ¬ t.closedBox ⊆ C₂.largeBox) :
    ∃ t', Relation.ReflTransGen (fun a b => SqAdj a b ∧ ¬ b.closedBox ⊆ C₂.largeBox) t t' ∧
      ¬ t'.closedBox ⊆ C₁.largeBox := by
  have hint : ¬ ((2 * C₂.j - 1 : ℤ) * 2 ^ (N - C₂.n - 1) ≤ t.j ∧
      (t.j : ℤ) + 1 ≤ (2 * C₂.j + 3) * 2 ^ (N - C₂.n - 1) ∧
      (2 * C₂.k - 1 : ℤ) * 2 ^ (N - C₂.n - 1) ≤ t.k ∧
      (t.k : ℤ) + 1 ≤ (2 * C₂.k + 3) * 2 ^ (N - C₂.n - 1)) := by
    rintro ⟨a1, a2, a3, a4⟩
    exact hout (bx_sub_of_int ht (fun z b1 b2 b3 b4 => (bx_mem_largeBox hN2).2
      ⟨b1, b2, b3, b4⟩) a1 a2 a3 a4)
  have hpos : 0 < 2 ^ N := by positivity
  have htj : t.j < 2 ^ N := ht ▸ t.hj
  have htk : t.k < 2 ^ N := ht ▸ t.hk
  have hlast : 2 ^ N - 1 < 2 ^ N := by omega
  have hte := sqAt_eq ht
  by_cases hcol : (2 * C₂.j - 1 : ℤ) * 2 ^ (N - C₂.n - 1) ≤ t.j ∧
      (t.j : ℤ) + 1 ≤ (2 * C₂.j + 3) * 2 ^ (N - C₂.n - 1)
  · -- the row of `t` lies outside `𝖢₂,large`
    have hrow : ∀ p (hp : p < 2 ^ N), ¬ (sqAt N p t.k hp htk).closedBox ⊆ C₂.largeBox := by
      intro p hp hsub
      obtain ⟨-, -, c3, c4⟩ := int_of_sub_largeBox rfl hN2 hsub
      exact hint ⟨hcol.1, hcol.2, c3, c4⟩
    by_cases h0 : (sqAt N 0 t.k hpos htk).closedBox ⊆ C₁.largeBox
    · refine ⟨sqAt N (2 ^ N - 1) t.k hlast htk, ?_, fun hsub => ?_⟩
      · convert row_path htk (fun b => ¬ b.closedBox ⊆ C₂.largeBox) hrow t.j _ htj hlast using 1
      · obtain ⟨c1, -, -, -⟩ := int_of_sub_largeBox rfl hN1 h0
        obtain ⟨-, c2, -, -⟩ := int_of_sub_largeBox rfl hN1 hsub
        simp only [sqAt] at c1 c2
        rw [two_pow_sub_one_cast] at c2
        exact largeBox_not_span h1 hN1 C₁.j ⟨by simpa using c1, c2⟩
    · exact ⟨sqAt N 0 t.k hpos htk, by convert row_path htk (fun b => ¬ b.closedBox ⊆ C₂.largeBox) hrow t.j _ htj hpos using 1, h0⟩
  · -- the column of `t` lies outside `𝖢₂,large`
    have hcl : ∀ q (hq : q < 2 ^ N), ¬ (sqAt N t.j q htj hq).closedBox ⊆ C₂.largeBox := by
      intro q hq hsub
      obtain ⟨c1, c2, -, -⟩ := int_of_sub_largeBox rfl hN2 hsub
      exact hcol ⟨c1, c2⟩
    by_cases h0 : (sqAt N t.j 0 htj hpos).closedBox ⊆ C₁.largeBox
    · refine ⟨sqAt N t.j (2 ^ N - 1) htj hlast, ?_, fun hsub => ?_⟩
      · convert col_path htj (fun b => ¬ b.closedBox ⊆ C₂.largeBox) hcl t.k _ htk hlast using 1
      · obtain ⟨-, -, c1, -⟩ := int_of_sub_largeBox rfl hN1 h0
        obtain ⟨-, -, -, c2⟩ := int_of_sub_largeBox rfl hN1 hsub
        simp only [sqAt] at c1 c2
        rw [two_pow_sub_one_cast] at c2
        exact largeBox_not_span h1 hN1 C₁.k ⟨by simpa using c1, c2⟩
    · exact ⟨sqAt N t.j 0 htj hpos, by convert col_path htj (fun b => ¬ b.closedBox ⊆ C₂.largeBox) hcl t.k _ htk hpos using 1, h0⟩

/-- **(F4) Nesting of enclosed regions** (the Jordan-type step behind DZZ's `i_r` recursion,
l. 1071–1079). If every square of `Y` is enclosed by the wall `X` in `𝖢₂,large`, and `a ∉ X` is
enclosed by `Y` in `𝖢₁,large` (`n_{𝖢₁} ≥ 1`), then `a` is enclosed by `X` in `𝖢₂,large`. -/
theorem not_esc_nest {X Y : Set DyBox} {C₁ C₂ a : DyBox} {N : ℕ} (h1 : 1 ≤ C₁.n)
    (hN1 : C₁.n + 1 ≤ N) (hN2 : C₂.n + 1 ≤ N) (hY : ∀ y ∈ Y, y ∉ X ∧ ¬ Esc X C₂.largeBox y)
    (ha : a.n = N) (haX : a ∉ X) (haY : ¬ Esc Y C₁.largeBox a) : ¬ Esc X C₂.largeBox a := by
  rintro ⟨-, t, hat, ht⟩
  -- the escaping path avoids `Y`
  have key : ∀ c, Relation.ReflTransGen (StepAv X) c t → Relation.ReflTransGen (StepAv Y) c t := by
    intro c hc
    induction hc using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head hcc' hc't ih =>
      rename_i c c'
      refine Relation.ReflTransGen.head ⟨hcc'.1, fun hc'Y => ?_⟩ ih
      exact (hY c' hc'Y).2 ⟨hcc'.2, t, hc't, ht⟩
  have haY' : a ∉ Y := fun h => (hY a h).2 ⟨haX, t, hat, ht⟩
  have htn : t.n = N := (reach_n (fun _ _ h => h.1) hat).trans ha
  obtain ⟨t', htt', ht'⟩ := exists_out_path h1 hN1 hN2 htn ht
  have hY2 : ∀ y ∈ Y, y.closedBox ⊆ C₂.largeBox := fun y hy => sub_of_not_esc (hY y hy).1 (hY y hy).2
  have hmono : ∀ c, Relation.ReflTransGen (fun a b => SqAdj a b ∧ ¬ b.closedBox ⊆ C₂.largeBox)
      t c → Relation.ReflTransGen (StepAv Y) t c := by
    intro c hc
    induction hc with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail ⟨h.1, fun hcY => h.2 (hY2 _ hcY)⟩
  exact haY ⟨haY', t', (key a hat).trans (hmono t' htt'), ht'⟩

end DZZ
end LQGMetric
