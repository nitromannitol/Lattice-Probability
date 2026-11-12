/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X7 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X6

/-!
# DZZ Lemma 3.12: blocks survive the removal of repeats (D93 §2, packet P-6a, coarse step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1471–1477),
ring form of DEC-93 §2: the closed walk of the coarse ring is assembled from crossings with
spurs (back-and-forth stretches), which may repeat boxes consecutively; removing consecutive
repeats (`dd`, S3L12W11) keeps the blocks of the parent cells. A block is the same as the
absence of a pattern `P, ¬P, P` in a sublist (`NoGap`), which passes to sublists.

* `dd_sublist`; `NoGap`, `noGap_sublist`, **`block_of_noGap`**, **`noGap_of_block`**.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

lemma dd_sublist : ∀ l : List DyBox, (dd l).Sublist l
  | [] => by simp [dd]
  | [a] => by simp [dd]
  | a :: b :: t => by
    have ih := dd_sublist (b :: t)
    simp only [dd]
    split_ifs
    · exact ih.cons a
    · exact ih.cons₂ a

/-- No `Q, ¬Q, Q` pattern in a sublist. -/
def NoGap {α : Type*} (Q : α → Prop) (L : List α) : Prop :=
  ∀ a b c, [a, b, c].Sublist L → Q a → Q c → Q b

lemma noGap_sublist {α : Type*} {Q : α → Prop} {L L' : List α} (h : L'.Sublist L)
    (hL : NoGap Q L) : NoGap Q L' :=
  fun a b c habc ha hc => hL a b c (habc.trans h) ha hc

/-- **A gap-free list is a block.** -/
lemma block_of_noGap {α : Type*} {Q : α → Prop} : ∀ L : List α, NoGap Q L →
    ∃ L₁ L₂ L₃ : List α, L = L₁ ++ L₂ ++ L₃ ∧ (∀ x ∈ L₂, Q x) ∧ ∀ x ∈ L₁ ++ L₃, ¬ Q x
  | [], _ => ⟨[], [], [], rfl, by simp, by simp⟩
  | a :: t, hL => by
    obtain ⟨T₁, T₂, T₃, rfl, h2, h13⟩ :=
      block_of_noGap t (noGap_sublist (List.sublist_cons_self a t) hL)
    by_cases ha : Q a
    · rcases T₁ with _ | ⟨x, T₁⟩
      · refine ⟨[], a :: T₂, T₃, rfl, ?_, by simpa using h13⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ha
        · exact h2 y hy
      · rcases T₂ with _ | ⟨y, T₂⟩
        · refine ⟨[], [a], x :: T₁ ++ T₃, by simp, by simpa using ha, ?_⟩
          simpa using h13
        · exfalso
          have hx : ¬ Q x := h13 x (by simp)
          exact hx (hL a x y (by simp) ha (h2 y (by simp)))
    · refine ⟨a :: T₁, T₂, T₃, rfl, h2, ?_⟩
      intro y hy
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hy
      rcases hy with rfl | hy | hy
      · exact ha
      · exact h13 y (List.mem_append_left _ hy)
      · exact h13 y (List.mem_append_right _ hy)

/-- **A block is gap-free.** -/
lemma noGap_of_block {α : Type*} {Q : α → Prop} {L₁ L₂ L₃ : List α}
    (h2 : ∀ x ∈ L₂, Q x) (h13 : ∀ x ∈ L₁ ++ L₃, ¬ Q x) : NoGap Q (L₁ ++ L₂ ++ L₃) := by
  intro a b c habc ha hc
  rw [List.append_assoc, List.sublist_append_iff] at habc
  obtain ⟨r₁, r₂, e, hr₁, hr₂⟩ := habc
  rcases r₁ with _ | ⟨x, r₁⟩
  · simp only [List.nil_append] at e
    subst e
    rw [List.sublist_append_iff] at hr₂
    obtain ⟨s₁, s₂, e', hs₁, hs₂⟩ := hr₂
    rcases List.eq_nil_or_concat s₂ with rfl | ⟨s₂', y, rfl⟩
    · simp only [List.append_nil] at e'
      subst e'
      exact h2 b (hs₁.subset (by simp))
    · exfalso
      have hy : y = c := by
        have := congrArg List.getLast? e'
        simp only [List.getLast?_cons_cons, List.getLast?_singleton,
          ← List.append_assoc, List.getLast?_append, List.getLast?_singleton] at this
        simpa using this.symm
      subst hy
      exact h13 y (List.mem_append_right _ (hs₂.subset (by simp))) hc
  · exfalso
    have hx : x = a := by simp only [List.cons_append, List.cons.injEq] at e; exact e.1.symm
    subst hx
    exact h13 x (List.mem_append_left _ (hr₁.subset (by simp))) ha

end DZZ
end LQGMetric
