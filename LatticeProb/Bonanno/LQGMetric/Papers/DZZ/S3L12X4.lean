/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X3

/-!
# DZZ Lemma 3.12: cutting a crossing at the zone slabs (D93 §2, packet P-6a, coarse step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1461–1477),
in the ring form of DEC-93 §2 ("producing each parent exactly once"): in a side rectangle of
the annulus, the zone of a parent cell is a slab `{long coordinate < s₁}` or
`{long coordinate ≥ s₂}` all of whose sites lie in the parent. A long-way crossing is replaced by
one that runs straight through the first slab, then follows the crossing (outside both slabs),
then runs straight through the second slab, so that each zone is visited in one block.

In the standard rectangle `[0, W] × [0, H]` (first coordinate = long coordinate):
* `stdRow`, `prefix_cut`, `suffix_cut` (by the reflection `x ↦ W - x`), **`slab_cut`**.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

/-- The standard rectangle `[0, W] × [0, H]`. -/
def StdRect (W H : ℤ) (z : ℤ × ℤ) : Prop := 0 ≤ z.1 ∧ z.1 ≤ W ∧ 0 ≤ z.2 ∧ z.2 ≤ H

/-- The site `(i, y)`. -/
def stdRowF (y : ℤ) (i : ℕ) : ℤ × ℤ := ((i : ℤ), y)

/-- The row from `(0, y)` to `(a, y)`. -/
def stdRow (a y : ℤ) : List (ℤ × ℤ) := (List.range (a.toNat + 1)).map (stdRowF y)

lemma stdRow_chain (a y : ℤ) : (stdRow a y).IsChain PercAdj4 := by
  unfold stdRow
  refine (List.isChain_map (stdRowF y)).2 ((List.isChain_range_succ _ _).2 fun m _ => ?_)
  right; refine ⟨rfl, Or.inr ?_⟩; simp [stdRowF]

lemma mem_stdRow {a y : ℤ} (ha : 0 ≤ a) {z : ℤ × ℤ} :
    z ∈ stdRow a y ↔ 0 ≤ z.1 ∧ z.1 ≤ a ∧ z.2 = y := by
  unfold stdRow
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    simp only [stdRowF]
    exact ⟨by positivity, by omega, trivial⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨z.1.toNat, List.mem_range.2 (by omega), ?_⟩
    ext
    · simp [stdRowF, Int.toNat_of_nonneg h1]
    · exact h3.symm

lemma stdRow_head (a y : ℤ) : (stdRow a y).head? = some (0, y) := by
  simp [stdRow, stdRowF, List.range_succ_eq_map]

lemma stdRow_last {a : ℤ} (ha : 0 ≤ a) (y : ℤ) : (stdRow a y).getLast? = some (a, y) := by
  simp [stdRow, stdRowF, List.range_succ, Int.toNat_of_nonneg ha]

lemma stdRow_ne (a y : ℤ) : stdRow a y ≠ [] := by
  intro h; have := stdRow_head a y; rw [h] at this; simp at this

/-- Splitting off the maximal suffix satisfying `Q` (any type). -/
lemma exists_suffix_split' {α : Type*} (Q : α → Prop) : ∀ F : List α,
    ∃ A T : List α, F = A ++ T ∧ (∀ y ∈ T, Q y) ∧ ∀ a ∈ A.getLast?, ¬ Q a
  | [] => ⟨[], [], rfl, by simp, by simp⟩
  | a :: F => by
    obtain ⟨A, T, rfl, hT, hA⟩ := exists_suffix_split' Q F
    rcases A with _ | ⟨x, A⟩
    · by_cases ha : Q a
      · refine ⟨[], a :: T, rfl, ?_, by simp⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ha
        · exact hT y hy
      · exact ⟨[a], T, rfl, hT, by simpa using ha⟩
    · refine ⟨a :: x :: A, T, rfl, hT, ?_⟩
      rw [List.getLast?_cons_cons]; exact hA

/-- **Prefix cut**: straight through `{x < s}` up to the last visit of the crossing there. -/
lemma prefix_cut {W H s : ℤ} (hs : 0 ≤ s) (l : List (ℤ × ℤ)) (hl : l.IsChain PercAdj4)
    (hR : ∀ z ∈ l, StdRect W H z) (h0 : ∀ a ∈ l.head?, a.1 = 0) (hne : l ≠ []) :
    ∃ A M : List (ℤ × ℤ), (A ++ M).IsChain PercAdj4 ∧ (∀ a ∈ (A ++ M).head?, a.1 = 0) ∧
      (A ++ M).getLast? = l.getLast? ∧ (A ++ M) ≠ [] ∧
      (∀ z ∈ A, StdRect W H z ∧ z.1 < s) ∧ (∀ z ∈ M, z ∈ l ∧ s ≤ z.1) := by
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · refine ⟨[], l, by simpa using hl, by simpa using h0, by simp, by simpa using hne, by simp,
      fun z hz => ⟨hz, hs0 ▸ (hR z hz).1⟩⟩
  obtain ⟨A', T, rfl, hT, hA'⟩ := exists_suffix_split' (fun z : ℤ × ℤ => s ≤ z.1) l
  have hA'0 : A' ≠ [] := by
    rintro rfl
    rcases T with _ | ⟨x, T⟩
    · exact hne rfl
    · have := h0 x (by simp); have := hT x (by simp); omega
  set u := A'.getLast hA'0
  have hu : u ∈ A'.getLast? := by simp [u, List.getLast?_eq_some_getLast hA'0]
  have hus : u.1 < s := lt_of_not_ge (hA' u hu)
  have huR := hR u (List.mem_append_left _ (List.getLast_mem _))
  rw [List.isChain_append] at hl
  refine ⟨stdRow u.1 u.2, T, ?_, ?_, ?_, ?_, ?_, fun z hz => ⟨List.mem_append_right _ hz, hT z hz⟩⟩
  · rw [List.isChain_append]
    refine ⟨stdRow_chain _ _, hl.2.1, fun x hx y hy => ?_⟩
    rw [stdRow_last huR.1] at hx
    cases hx
    exact hl.2.2 u hu y hy
  · rw [List.head?_append_of_ne_nil _ (stdRow_ne _ _), stdRow_head]; intro a ha; cases ha; rfl
  · rcases T with _ | ⟨x, T⟩
    · simp only [List.append_nil]; rw [stdRow_last huR.1, ← hu]
    · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
        List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
  · simp [stdRow_ne]
  · intro z hz
    obtain ⟨z1, z2, z3⟩ := (mem_stdRow huR.1).1 hz
    have := huR.2.1
    exact ⟨⟨z1, by omega, by rw [z3]; exact huR.2.2.1, by rw [z3]; exact huR.2.2.2⟩, by omega⟩

/-- The reflection `x ↦ W - x`. -/
def stdRefl (W : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (W - z.1, z.2)

lemma stdRefl_refl (W : ℤ) (z : ℤ × ℤ) : stdRefl W (stdRefl W z) = z := by
  simp [stdRefl]

lemma adj4_stdRefl {W : ℤ} {x y : ℤ × ℤ} (h : PercAdj4 x y) : PercAdj4 (stdRefl W y) (stdRefl W x) := by
  unfold PercAdj4 stdRefl at *; simp only at *; omega

lemma chain_refl {W : ℤ} {l : List (ℤ × ℤ)} (h : l.IsChain PercAdj4) :
    (l.map (stdRefl W)).reverse.IsChain PercAdj4 := by
  rw [List.isChain_reverse, List.isChain_map]
  exact h.imp fun a b hab => adj4_stdRefl hab

/-- **Suffix cut**: straight through `{x ≥ s}` from the first visit of the crossing there. -/
lemma suffix_cut {W H s : ℤ} (hs : s ≤ W + 1) (l : List (ℤ × ℤ)) (hl : l.IsChain PercAdj4)
    (hR : ∀ z ∈ l, StdRect W H z) (hW : ∀ b ∈ l.getLast?, b.1 = W) (hne : l ≠ []) :
    ∃ M B : List (ℤ × ℤ), (M ++ B).IsChain PercAdj4 ∧ (∀ b ∈ (M ++ B).getLast?, b.1 = W) ∧
      (M ++ B).head? = l.head? ∧
      (∀ z ∈ M, z ∈ l ∧ z.1 < s) ∧ (∀ z ∈ B, StdRect W H z ∧ s ≤ z.1) := by
  set l' := (l.map (stdRefl W)).reverse
  have hR' : ∀ z ∈ l', StdRect W H z := by
    intro z hz
    simp only [l', List.mem_reverse, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨a1, a2, a3, a4⟩ := hR y hy
    exact ⟨by simp [stdRefl]; omega, by simp [stdRefl]; omega, a3, a4⟩
  have h0' : ∀ a ∈ l'.head?, a.1 = 0 := by
    intro a ha
    simp only [l', List.head?_reverse, List.getLast?_map, Option.mem_def,
      Option.map_eq_some_iff] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    simp [stdRefl, hW b hb]
  obtain ⟨A, M', hc, hc0, hlast, -, hA, hM⟩ := prefix_cut (W := W) (H := H) (s := W + 1 - s)
    (by omega) l' (chain_refl hl) hR' h0' (by simpa [l'] using hne)
  have e : (M'.map (stdRefl W)).reverse ++ (A.map (stdRefl W)).reverse =
      ((A ++ M').map (stdRefl W)).reverse := by
    rw [List.map_append, List.reverse_append]
  refine ⟨(M'.map (stdRefl W)).reverse, (A.map (stdRefl W)).reverse, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact chain_refl hc
  · intro b hb
    rw [e, List.getLast?_reverse, List.head?_map, Option.mem_def, Option.map_eq_some_iff] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simp [stdRefl, hc0 a ha]
  · rw [e, List.head?_reverse, List.getLast?_map, hlast]
    simp only [l', List.getLast?_reverse, List.head?_map, Option.map_map]
    rcases l with _ | ⟨x, l⟩
    · rfl
    · simp [stdRefl_refl]
  · intro z hz
    simp only [List.mem_reverse, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨hyl, hys⟩ := hM y hy
    simp only [l', List.mem_reverse, List.mem_map] at hyl
    obtain ⟨w, hw, rfl⟩ := hyl
    refine ⟨by rw [stdRefl_refl]; exact hw, ?_⟩
    simp only [stdRefl] at hys ⊢; omega
  · intro z hz
    simp only [List.mem_reverse, List.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨⟨a1, a2, a3, a4⟩, hys⟩ := hA y hy
    simp only [StdRect, stdRefl]
    omega

/-- **Slab cut** of a long-way crossing of `[0, W] × [0, H]` by sites of `G`: straight through
`{x < s₁}`, then the crossing inside `{s₁ ≤ x < s₂}`, then straight through `{x ≥ s₂}`. -/
theorem slab_cut {W H s₁ s₂ : ℤ} (hs₁ : 0 ≤ s₁) (hs₂ : s₂ ≤ W + 1) {G : Set (ℤ × ℤ)}
    (l : List (ℤ × ℤ)) (hl : l.IsChain PercAdj4) (hR : ∀ z ∈ l, StdRect W H z ∧ z ∈ G)
    (h0 : ∀ a ∈ l.head?, a.1 = 0) (hW : ∀ b ∈ l.getLast?, b.1 = W) (hne : l ≠ []) :
    ∃ A M B : List (ℤ × ℤ), (A ++ M ++ B).IsChain PercAdj4 ∧ (A ++ M ++ B) ≠ [] ∧
      (∀ a ∈ (A ++ M ++ B).head?, a.1 = 0) ∧ (∀ b ∈ (A ++ M ++ B).getLast?, b.1 = W) ∧
      (∀ z ∈ A, StdRect W H z ∧ z.1 < s₁) ∧
      (∀ z ∈ M, StdRect W H z ∧ z ∈ G ∧ s₁ ≤ z.1 ∧ z.1 < s₂) ∧
      (∀ z ∈ B, StdRect W H z ∧ s₂ ≤ z.1) := by
  obtain ⟨A, M₀, hc, hc0, hlast, hne', hA, hM₀⟩ :=
    prefix_cut hs₁ l hl (fun z hz => (hR z hz).1) h0 hne
  rcases M₀ with _ | ⟨x, M₀⟩
  · refine ⟨A, [], [], by simpa using hc, by simpa using hne', by simpa using hc0, ?_,
      hA, by simp, by simp⟩
    simp only [List.append_nil] at hlast ⊢; rw [hlast]; exact hW
  rw [List.isChain_append] at hc
  obtain ⟨M, B, hc', hW', hhead, hM, hB⟩ := suffix_cut (H := H) hs₂ (x :: M₀) hc.2.1
    (fun z hz => (hR z (hM₀ z hz).1).1)
    (by
      intro b hb
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hlast
      rw [hlast] at hb; exact hW b hb)
    (List.cons_ne_nil _ _)
  have hMB : M ++ B ≠ [] := by intro h; rw [h] at hhead; simp at hhead
  refine ⟨A, M, B, ?_, by simp [hMB], ?_, ?_, hA, ?_, hB⟩
  · rw [List.append_assoc, List.isChain_append]
    refine ⟨hc.1, hc', fun a ha b hb => hc.2.2 a ha b (by rw [← hhead]; exact hb)⟩
  · rw [List.append_assoc]
    rcases A with _ | ⟨y, A⟩
    · intro a ha; rw [List.nil_append, hhead] at ha
      exact hc0 a (by simpa using ha)
    · intro a ha; exact hc0 a (by simpa using ha)
  · rw [List.append_assoc, List.getLast?_append_of_ne_nil _ hMB]; exact hW'
  · intro z hz
    obtain ⟨hz1, hz2⟩ := hM z hz
    obtain ⟨hzl, hzs⟩ := hM₀ z hz1
    exact ⟨(hR z hzl).1, (hR z hzl).2, hzs, hz2⟩

end DZZ
end LQGMetric
