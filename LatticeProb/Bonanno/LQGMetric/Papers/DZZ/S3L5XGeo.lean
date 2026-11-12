/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5XGeo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5XAdj

/-!
# DZZ Lemma 3.5: the `δ`-geodesic as a path of grid squares (P2-DEC84, D84)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1067): "suppose `𝖢_1, ⋯, 𝖢_d` is a
sequence of neighboring cells in `𝒱_δ` joining `u` to `v`". On the level-`N` grid (decision D84)
the cells of a walk in `cellGraph m δ` are traversed by a 4-path of squares, labelled by the index
of the cell containing them (labels nondecreasing, steps `≤ 1`): the input of `l35_recursion`.

* `rtg_to_fun`: a `ReflTransGen` chain as a function `ℕ → α`.
* `path_in_box`: two squares of a box are joined by a 4-path of squares of the box.
* **`exists_labelled_path`**: the labelled path along a walk of cells.

Own elementary arguments; DEVIATIONS DV-D84.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma rtg_to_fun {α : Type*} {R : α → α → Prop} {a b : α} (h : Relation.ReflTransGen R a b) :
    ∃ M : ℕ, ∃ f : ℕ → α, f 0 = a ∧ f M = b ∧ ∀ t < M, R (f t) (f (t + 1)) := by
  classical
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun t ht => absurd ht (by omega)⟩
  | tail _ hbc ih =>
    rename_i b c _
    obtain ⟨M, f, h0, hM, hs⟩ := ih
    refine ⟨M + 1, fun t => if t ≤ M then f t else c, by simp [h0], by simp, fun t ht => ?_⟩
    rcases Nat.lt_or_ge t M with h | h
    · simp only [if_pos h.le, if_pos (show t + 1 ≤ M by omega)]; exact hs t h
    · obtain rfl : t = M := by omega
      simp only [le_refl, if_true, show ¬ t + 1 ≤ t by omega, if_false, hM]; exact hbc

/-- Horizontal 4-paths along a segment of a row whose squares satisfy `P`. -/
lemma row_seg {N q : ℕ} (hq : q < 2 ^ N) (P : DyBox → Prop) :
    ∀ d p (hp : p < 2 ^ N) (hd : p + d < 2 ^ N),
      (∀ i (hi : i < 2 ^ N), p ≤ i → i ≤ p + d → P (sqAt N i q hi hq)) →
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N p q hp hq) (sqAt N (p + d) q hd hq) ∧
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N (p + d) q hd hq) (sqAt N p q hp hq) := by
  intro d
  induction d with
  | zero => intros; exact ⟨.refl, .refl⟩
  | succ d ih =>
    intro p hp hd hP
    obtain ⟨h1, h2⟩ := ih p hp (by omega) fun i hi a b => hP i hi a (by omega)
    refine ⟨h1.tail ⟨⟨rfl, Or.inr ⟨rfl, Or.inl (by simp [sqAt]; omega)⟩⟩, hP _ _ (by omega) le_rfl⟩, ?_⟩
    exact Relation.ReflTransGen.head (b := sqAt N (p + d) q (by omega) hq)
      ⟨⟨rfl, Or.inr ⟨rfl, Or.inr (by simp [sqAt]; omega)⟩⟩, hP _ _ (by omega) (by omega)⟩ h2

/-- Vertical 4-paths along a segment of a column whose squares satisfy `P`. -/
lemma col_seg {N p : ℕ} (hp : p < 2 ^ N) (P : DyBox → Prop) :
    ∀ d q (hq : q < 2 ^ N) (hd : q + d < 2 ^ N),
      (∀ i (hi : i < 2 ^ N), q ≤ i → i ≤ q + d → P (sqAt N p i hp hi)) →
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N p q hp hq) (sqAt N p (q + d) hp hd) ∧
      Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N p (q + d) hp hd) (sqAt N p q hp hq) := by
  intro d
  induction d with
  | zero => intros; exact ⟨.refl, .refl⟩
  | succ d ih =>
    intro q hq hd hP
    obtain ⟨h1, h2⟩ := ih q hq (by omega) fun i hi a b => hP i hi a (by omega)
    refine ⟨h1.tail ⟨⟨rfl, Or.inl ⟨rfl, Or.inl (by simp [sqAt]; omega)⟩⟩, hP _ _ (by omega) le_rfl⟩, ?_⟩
    exact Relation.ReflTransGen.head (b := sqAt N p (q + d) hp (by omega))
      ⟨⟨rfl, Or.inl ⟨rfl, Or.inr (by simp [sqAt]; omega)⟩⟩, hP _ _ (by omega) (by omega)⟩ h2

lemma sq_sub_of_bounds {C : DyBox} {N : ℕ} (hC : C.n ≤ N) {i q : ℕ} (hi : i < 2 ^ N)
    (hq : q < 2 ^ N) (h1 : C.j * 2 ^ (N - C.n) ≤ i) (h2 : i + 1 ≤ (C.j + 1) * 2 ^ (N - C.n))
    (h3 : C.k * 2 ^ (N - C.n) ≤ q) (h4 : q + 1 ≤ (C.k + 1) * 2 ^ (N - C.n)) :
    (sqAt N i q hi hq).closedBox ⊆ C.closedBox :=
  bx_sub_closedBox rfl hC (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3)
    (by exact_mod_cast h4)

/-- Two level-`N` squares of a box are joined by a 4-path of level-`N` squares of the box. -/
lemma path_in_box {C : DyBox} {N : ℕ} (hC : C.n ≤ N) {s t : DyBox} (hs : s.n = N) (ht : t.n = N)
    (hsC : s.closedBox ⊆ C.closedBox) (htC : t.closedBox ⊆ C.closedBox) :
    Relation.ReflTransGen (fun a b => SqAdj a b ∧ (b.n = N ∧ b.closedBox ⊆ C.closedBox)) s t := by
  obtain ⟨s1, s2, s3, s4⟩ := int_of_sub_closedBox hs hC hsC
  obtain ⟨t1, t2, t3, t4⟩ := int_of_sub_closedBox ht hC htC
  have hsj : s.j < 2 ^ N := hs ▸ s.hj
  have hsk : s.k < 2 ^ N := hs ▸ s.hk
  have htj : t.j < 2 ^ N := ht ▸ t.hj
  have htk : t.k < 2 ^ N := ht ▸ t.hk
  set P : DyBox → Prop := fun b => b.n = N ∧ b.closedBox ⊆ C.closedBox
  have row : Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N s.j s.k hsj hsk)
      (sqAt N t.j s.k htj hsk) := by
    rcases le_total s.j t.j with h | h
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      have := (row_seg hsk P d s.j hsj (by omega) fun i hi a b =>
        ⟨rfl, sq_sub_of_bounds hC hi hsk (by omega) (by omega) s3 s4⟩).1
      convert this using 2
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      have := (row_seg hsk P d t.j htj (by omega) fun i hi a b =>
        ⟨rfl, sq_sub_of_bounds hC hi hsk (by omega) (by omega) s3 s4⟩).2
      convert this using 2
  have col : Relation.ReflTransGen (fun a b => SqAdj a b ∧ P b) (sqAt N t.j s.k htj hsk)
      (sqAt N t.j t.k htj htk) := by
    rcases le_total s.k t.k with h | h
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      have := (col_seg htj P d s.k hsk (by omega) fun i hi a b =>
        ⟨rfl, sq_sub_of_bounds hC htj hi t1 t2 (by omega) (by omega)⟩).1
      convert this using 2
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
      have := (col_seg htj P d t.k htk (by omega) fun i hi a b =>
        ⟨rfl, sq_sub_of_bounds hC htj hi t1 t2 (by omega) (by omega)⟩).2
      convert this using 2
  have e1 := sqAt_eq hs
  have e2 := sqAt_eq ht
  convert row.trans col using 1

/-- Labelled steps: equal or 4-adjacent squares, label constant or `+1`, target square of level
`N` inside the cell of its label. -/
def LRel (N : ℕ) (C : ℕ → DyBox) (x y : DyBox × ℕ) : Prop :=
  (x.1 = y.1 ∨ SqAdj x.1 y.1) ∧ (y.2 = x.2 ∨ y.2 = x.2 + 1) ∧ y.1.n = N ∧
    y.1.closedBox ⊆ (C y.2).closedBox

lemma lift_label {N L : ℕ} {C : ℕ → DyBox} {x y : DyBox}
    (h : Relation.ReflTransGen (fun a b => SqAdj a b ∧ (b.n = N ∧ b.closedBox ⊆ (C L).closedBox))
      x y) : Relation.ReflTransGen (LRel N C) (x, L) (y, L) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail ⟨Or.inr hbc.1, Or.inl rfl, hbc.2.1, hbc.2.2⟩

/-- **The labelled path along a walk of cells** (all cells of level `≤ N`). -/
theorem exists_labelled_rtg {N : ℕ} (hN : ∀ b, IsCell m δ b → b.n ≤ N) {T T' : DyBox}
    (w : (cellGraph m δ).Walk T T') : IsCell m δ T → ∀ s₀ s₁ : DyBox, s₀.n = N →
      s₀.closedBox ⊆ T.closedBox → s₁.n = N → s₁.closedBox ⊆ T'.closedBox →
      Relation.ReflTransGen (LRel N fun i => w.getVert i) (s₀, 0) (s₁, w.length) := by
  induction w with
  | nil =>
    rename_i u
    intro hT s₀ s₁ h0 h0T h1 h1T
    exact lift_label (C := fun i => (SimpleGraph.Walk.nil : (cellGraph m δ).Walk u u).getVert i)
      (L := 0) (path_in_box (hN u hT) h0 h1 h0T h1T)
  | cons hadj w' ih =>
    rename_i u v x
    intro hT s₀ s₁ h0 h0T h1 h1T
    obtain ⟨a, b, han, hau, hbv, hab⟩ := exists_sqAdj_of_neighbour hadj.1 hadj.2.1
      (hN _ hadj.1) (hN _ hadj.2.1) hadj.2.2
    have p1 := path_in_box (hN u hT) h0 han h0T hau
    have q1 : Relation.ReflTransGen (LRel N fun i => (SimpleGraph.Walk.cons hadj w').getVert i)
        (s₀, 0) (a, 0) := lift_label p1
    have hbn : b.n = N := hab.1 ▸ han
    have q2 := ih hadj.2.1 b s₁ hbn hbv h1 h1T
    have q3 : Relation.ReflTransGen (LRel N fun i => (SimpleGraph.Walk.cons hadj w').getVert i)
        (b, 1) (s₁, w'.length + 1) := by
      have key : ∀ y, Relation.ReflTransGen (LRel N fun i => w'.getVert i) (b, 0) y →
          Relation.ReflTransGen (LRel N fun i => (SimpleGraph.Walk.cons hadj w').getVert i)
            (b, 1) (y.1, y.2 + 1) := by
        intro y hy
        induction hy with
        | refl => exact .refl
        | tail _ hbc ih' =>
          refine ih'.tail ⟨hbc.1, ?_, hbc.2.2.1, ?_⟩
          · rcases hbc.2.1 with e | e
            · exact Or.inl (by rw [e])
            · exact Or.inr (by rw [e])
          · simp only [SimpleGraph.Walk.getVert_cons_succ]; exact hbc.2.2.2
      exact key _ q2
    rw [SimpleGraph.Walk.length_cons]
    refine (q1.tail ⟨Or.inr hab, Or.inr rfl, hbn, ?_⟩).trans q3
    simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero]
    exact hbv

lemma le_of_mono_steps {lab : ℕ → ℕ} {M : ℕ} (h : ∀ t < M, lab t ≤ lab (t + 1)) :
    ∀ k t, t + k = M → lab t ≤ lab M := by
  intro k
  induction k with
  | zero => intro t ht; rw [← ht]; rfl
  | succ k ih => intro t ht; exact (h t (by omega)).trans (ih (t + 1) (by omega))

/-- **The `δ`-geodesic as a labelled path of squares**, in the form used by `l35_recursion`. -/
theorem exists_labelled_path {N : ℕ} (hN : ∀ b, IsCell m δ b → b.n ≤ N) {T T' : DyBox}
    (w : (cellGraph m δ).Walk T T') (hT : IsCell m δ T) (s₀ s₁ : DyBox) (h0 : s₀.n = N)
    (h0T : s₀.closedBox ⊆ T.closedBox) (h1 : s₁.n = N) (h1T : s₁.closedBox ⊆ T'.closedBox) :
    ∃ M : ℕ, ∃ p : ℕ → DyBox, ∃ lab : ℕ → ℕ, p 0 = s₀ ∧ p M = s₁ ∧ lab 0 = 0 ∧
      lab M = w.length ∧
      (∀ t ≤ M, (p t).n = N ∧ lab t ≤ w.length ∧ (p t).closedBox ⊆ (w.getVert (lab t)).closedBox) ∧
      ∀ t < M, (p t = p (t + 1) ∨ SqAdj (p t) (p (t + 1))) ∧ lab t ≤ lab (t + 1) ∧
        lab (t + 1) ≤ lab t + 1 := by
  obtain ⟨M, f, hf0, hfM, hs⟩ := rtg_to_fun (exists_labelled_rtg hN w hT s₀ s₁ h0 h0T h1 h1T)
  have hmono : ∀ t < M, (f t).2 ≤ (f (t + 1)).2 ∧ (f (t + 1)).2 ≤ (f t).2 + 1 := fun t ht => by
    rcases (hs t ht).2.1 with e | e <;> omega
  refine ⟨M, fun t => (f t).1, fun t => (f t).2, by simp only [hf0], by simp only [hfM],
    by simp only [hf0], by simp only [hfM], fun t ht => ?_, fun t ht => ⟨(hs t ht).1, hmono t ht⟩⟩
  have hle : (f t).2 ≤ w.length := by
    have := le_of_mono_steps (lab := fun t => (f t).2) (fun t ht => (hmono t ht).1) (M - t) t
      (by omega)
    simp only [hfM] at this; exact this
  rcases Nat.eq_zero_or_pos t with rfl | hpos
  · simp only [hf0, SimpleGraph.Walk.getVert_zero]; exact ⟨h0, Nat.zero_le _, h0T⟩
  · obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_lt hpos
    have := hs t' (by omega)
    simp only [zero_add] at this hle ⊢
    exact ⟨this.2.2.1, hle, this.2.2.2⟩

end DZZ
end LQGMetric
