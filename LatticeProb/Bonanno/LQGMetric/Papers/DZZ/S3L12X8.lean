/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X7

/-!
# DZZ Lemma 3.12: spurs and closing a walk (D93 §2, packet P-6a, coarse step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1471–1477),
ring form of DEC-93 §2: the part of the closed walk along one side runs from the meeting point
with the previous side back to the start of the side's crossing, along the whole crossing, and
back to the meeting point with the next side (so that the walk contains the four crossings,
which give the separation, `enclosesBox_of_hasCross`); a closed walk of boxes with repeats gives
a cyclic `Neighbour`-list (`dd`, then drop the closing box).

* `EqOr`, **`spur_walk`**; **`cyc_of_closed`**; **`walk_noGap`** (the parent blocks of the closed
  walk, abstract form).

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

open DyBox

/-- Equal or related. -/
def EqOr {α : Type*} (r : α → α → Prop) (x y : α) : Prop := x = y ∨ r x y

lemma isChain_reverse_symm {α : Type*} {r : α → α → Prop} (hs : ∀ x y, r x y → r y x)
    {l : List α} (h : l.IsChain r) : l.reverse.IsChain r := by
  rw [List.isChain_reverse]; exact h.imp fun a b hab => hs a b hab

/-- **The spur walk along `Y` from `u` to `v` through all of `Y`.** -/
theorem spur_walk {α : Type*} {r : α → α → Prop} (hs : ∀ x y, r x y → r y x) {Y : List α}
    (hY : Y.IsChain r) {Y₁ Y₂ Z₁ Z₂ : List α} {u v : α} (e₁ : Y = Y₁ ++ u :: Y₂)
    (e₂ : Y = Z₁ ++ v :: Z₂) :
    ((Y₁ ++ [u]).reverse ++ Y ++ (v :: Z₂).reverse).IsChain (EqOr r) ∧
      ((Y₁ ++ [u]).reverse ++ Y ++ (v :: Z₂).reverse).head? = some u ∧
      ((Y₁ ++ [u]).reverse ++ Y ++ (v :: Z₂).reverse).getLast? = some v ∧
      ∀ x, x ∈ (Y₁ ++ [u]).reverse ++ Y ++ (v :: Z₂).reverse ↔ x ∈ Y := by
  have hY' := hY
  have hp : (Y₁ ++ [u]).IsChain r := by
    rw [e₁, show Y₁ ++ u :: Y₂ = (Y₁ ++ [u]) ++ Y₂ by simp] at hY'
    exact (List.isChain_append.1 hY').1
  have hq : (v :: Z₂).IsChain r := by
    have h := hY; rw [e₂] at h; exact (List.isChain_append.1 h).2.1
  have hYne : Y ≠ [] := by rw [e₁]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.isChain_append, List.isChain_append]
    refine ⟨⟨(isChain_reverse_symm hs hp).imp fun _ _ h => Or.inr h,
      hY.imp fun _ _ h => Or.inr h, ?_⟩,
      (isChain_reverse_symm hs hq).imp fun _ _ h => Or.inr h, ?_⟩
    · intro a ha b hb
      left
      rw [List.getLast?_reverse] at ha
      have : (Y₁ ++ [u]).head? = Y.head? := by
        rw [e₁]; rcases Y₁ with _ | ⟨x, Y₁⟩ <;> simp
      rw [this] at ha
      rw [ha] at hb; exact Option.some_injective _ hb
    · intro a ha b hb
      left
      rw [List.getLast?_append_of_ne_nil _ hYne] at ha
      rw [List.head?_reverse] at hb
      have : (v :: Z₂).getLast? = Y.getLast? := by
        rw [e₂, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rw [this, ha] at hb; exact Option.some_injective _ hb
  · rw [List.append_assoc, List.head?_append_of_ne_nil _ (by simp)]; simp
  · rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_reverse]; rfl
  · intro x
    constructor
    · intro hx
      simp only [List.mem_append, List.mem_reverse] at hx
      rcases hx with (hx | hx) | hx
      · rw [e₁]; simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx <;> simp [hx]
      · exact hx
      · rw [e₂]; exact List.mem_append_right _ hx
    · intro hx; exact List.mem_append_left _ (List.mem_append_right _ hx)

/-- **A closed walk of boxes gives a cyclic `Neighbour`-list** with the same boxes. -/
theorem cyc_of_closed {W : List DyBox} (hW : W.IsChain (EqOr Neighbour)) (hne : W ≠ [])
    (hcl : W.head? = W.getLast?) (hnt : ∃ x ∈ W, ∃ y ∈ W, x ≠ y) :
    ∃ Z : List DyBox, Z ≠ [] ∧ CycChain Z ∧ Z.Sublist W ∧ ∀ x, x ∈ Z ↔ x ∈ W := by
  obtain ⟨w₀, W', rfl⟩ := List.exists_cons_of_ne_nil hne
  set D := dd (w₀ :: W')
  have hD : D.IsChain Neighbour := isChain_dd _ hW
  have hDh : D.head? = some w₀ := dd_head w₀ W'
  have hDl : D.getLast? = some w₀ := by
    rw [dd_getLast, ← hcl]; rfl
  have hDne : D ≠ [] := dd_ne_nil w₀ W'
  obtain ⟨D', w, eD⟩ : ∃ D' w, D = D' ++ [w] := by
    rcases List.eq_nil_or_concat D with h | ⟨D', w, h⟩
    · exact absurd h hDne
    · exact ⟨D', w, by simpa using h⟩
  have hw : w = w₀ := by
    have := hDl; rw [eD, List.getLast?_append_of_ne_nil _ (by simp)] at this; simpa using this
  subst hw
  have hD'ne : D' ≠ [] := by
    rintro rfl
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    have hx' := (mem_dd _ x).2 hx
    have hy' := (mem_dd _ y).2 hy
    rw [show dd (w :: W') = D from rfl, eD] at hx' hy'
    simp only [List.nil_append, List.mem_singleton] at hx' hy'
    exact hxy (hx'.trans hy'.symm)
  have hD'h : D'.head? = some w := by
    have := hDh; rw [eD, List.head?_append_of_ne_nil _ hD'ne] at this; exact this
  rw [eD, List.isChain_append] at hD
  refine ⟨D', hD'ne, ⟨hD.1, fun a ha b hb => ?_⟩, ?_, fun x => ?_⟩
  · rw [hD'h] at hb; cases hb
    exact hD.2.2 a ha w (by simp)
  · exact (List.sublist_append_left D' [w]).trans (eD ▸ dd_sublist _)
  · have key := mem_dd (w :: W') x
    rw [show dd (w :: W') = D from rfl, eD, List.mem_append, List.mem_singleton] at key
    rw [← key]
    constructor
    · exact fun h => Or.inl h
    · rintro (h | rfl)
      · exact h
      · rcases D' with _ | ⟨y, D'⟩
        · exact absurd rfl hD'ne
        · simp only [List.head?_cons, Option.some.injEq] at hD'h
          rw [hD'h]; exact List.mem_cons_self

set_option hygiene false in
/-- Closing the membership goals of `walk_noGap`. -/
macro "wclose" : tactic => `(tactic| first
  | exact hL₁ | exact hH₄ | exact hF₁ | exact hF₂ | exact hF₃ | exact hF₄
  | exact fun x h => (hH₁ x h).2 k₁ | exact fun x h => (hL₂ x h).2 k₁
  | exact fun x h => (hH₂ x h).2 k₂ | exact fun x h => (hL₃ x h).2 k₂
  | exact fun x h => (hH₃ x h).2 k₃ | exact fun x h => (hL₄ x h).2 k₃
  | exact fun x h hq => k₁ ((hH₁ x h).1 hq) | exact fun x h hq => k₁ ((hL₂ x h).1 hq)
  | exact fun x h hq => k₂ ((hH₂ x h).1 hq) | exact fun x h hq => k₂ ((hL₃ x h).1 hq)
  | exact fun x h hq => k₃ ((hH₃ x h).1 hq) | exact fun x h hq => k₃ ((hL₄ x h).1 hq)
  | simp)

/-- **Blocks of the closed walk** (abstract form): the walk is the concatenation of the four
side parts `Lᵢ ++ Fᵢ ++ Hᵢ` (in walk order, starting and ending at the home corner); `Fᵢ` is
outside every parent, `Hᵢ` and `Lᵢ₊₁` lie at the corner `i`, inside `P` iff `κᵢ`; a side with
both corners in `P` has `Fᵢ = []`; corners `1` and `3` in `P` force corner `2` in `P`. -/
theorem walk_noGap {α : Type*} {Q : α → Prop} {L₁ F₁ H₁ L₂ F₂ H₂ L₃ F₃ H₃ L₄ F₄ H₄ : List α}
    {κ₁ κ₂ κ₃ : Prop} (hL₁ : ∀ x ∈ L₁, ¬ Q x) (hH₄ : ∀ x ∈ H₄, ¬ Q x)
    (hF₁ : ∀ x ∈ F₁, ¬ Q x) (hF₂ : ∀ x ∈ F₂, ¬ Q x) (hF₃ : ∀ x ∈ F₃, ¬ Q x)
    (hF₄ : ∀ x ∈ F₄, ¬ Q x)
    (hH₁ : ∀ x ∈ H₁, Q x ↔ κ₁) (hL₂ : ∀ x ∈ L₂, Q x ↔ κ₁)
    (hH₂ : ∀ x ∈ H₂, Q x ↔ κ₂) (hL₃ : ∀ x ∈ L₃, Q x ↔ κ₂)
    (hH₃ : ∀ x ∈ H₃, Q x ↔ κ₃) (hL₄ : ∀ x ∈ L₄, Q x ↔ κ₃)
    (e₂ : κ₁ → κ₂ → F₂ = []) (e₃ : κ₂ → κ₃ → F₃ = []) (h13 : κ₁ → κ₃ → κ₂) :
    NoGap Q (L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂ ++ H₂) ++ (L₃ ++ F₃ ++ H₃) ++ (L₄ ++ F₄ ++ H₄)) := by
  by_cases k₁ : κ₁ <;> by_cases k₂ : κ₂ <;> by_cases k₃ : κ₃
  · rw [e₂ k₁ k₂, e₃ k₂ k₃]
    have e : L₁ ++ F₁ ++ H₁ ++ (L₂ ++ [] ++ H₂) ++ (L₃ ++ [] ++ H₃) ++ (L₄ ++ F₄ ++ H₄) =
        (L₁ ++ F₁) ++ (H₁ ++ L₂ ++ H₂ ++ L₃ ++ H₃ ++ L₄) ++ (F₄ ++ H₄) := by simp
    rw [e]
    refine noGap_of_block ?_ ?_ <;> (try simp only [List.forall_mem_append]) <;>
      (try constructorm* _ ∧ _) <;> wclose
  · rw [e₂ k₁ k₂]
    have e : L₁ ++ F₁ ++ H₁ ++ (L₂ ++ [] ++ H₂) ++ (L₃ ++ F₃ ++ H₃) ++ (L₄ ++ F₄ ++ H₄) =
        (L₁ ++ F₁) ++ (H₁ ++ L₂ ++ H₂ ++ L₃) ++ (F₃ ++ H₃ ++ (L₄ ++ F₄ ++ H₄)) := by simp
    rw [e]
    refine noGap_of_block ?_ ?_ <;> (try simp only [List.forall_mem_append]) <;>
      (try constructorm* _ ∧ _) <;> wclose
  · exact absurd (h13 k₁ k₃) k₂
  · have e : L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂ ++ H₂) ++ (L₃ ++ F₃ ++ H₃) ++ (L₄ ++ F₄ ++ H₄) =
        (L₁ ++ F₁) ++ (H₁ ++ L₂) ++ (F₂ ++ H₂ ++ (L₃ ++ F₃ ++ H₃) ++ (L₄ ++ F₄ ++ H₄)) := by simp
    rw [e]
    refine noGap_of_block ?_ ?_ <;> (try simp only [List.forall_mem_append]) <;>
      (try constructorm* _ ∧ _) <;> wclose
  · rw [e₃ k₂ k₃]
    have e : L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂ ++ H₂) ++ (L₃ ++ [] ++ H₃) ++ (L₄ ++ F₄ ++ H₄) =
        (L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂)) ++ (H₂ ++ L₃ ++ H₃ ++ L₄) ++ (F₄ ++ H₄) := by simp
    rw [e]
    refine noGap_of_block ?_ ?_ <;> (try simp only [List.forall_mem_append]) <;>
      (try constructorm* _ ∧ _) <;> wclose
  · have e : L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂ ++ H₂) ++ (L₃ ++ F₃ ++ H₃) ++ (L₄ ++ F₄ ++ H₄) =
        (L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂)) ++ (H₂ ++ L₃) ++ (F₃ ++ H₃ ++ (L₄ ++ F₄ ++ H₄)) := by simp
    rw [e]
    refine noGap_of_block ?_ ?_ <;> (try simp only [List.forall_mem_append]) <;>
      (try constructorm* _ ∧ _) <;> wclose
  · have e : L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂ ++ H₂) ++ (L₃ ++ F₃ ++ H₃) ++ (L₄ ++ F₄ ++ H₄) =
        (L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂ ++ H₂) ++ (L₃ ++ F₃)) ++ (H₃ ++ L₄) ++ (F₄ ++ H₄) := by simp
    rw [e]
    refine noGap_of_block ?_ ?_ <;> (try simp only [List.forall_mem_append]) <;>
      (try constructorm* _ ∧ _) <;> wclose
  · have e : L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂ ++ H₂) ++ (L₃ ++ F₃ ++ H₃) ++ (L₄ ++ F₄ ++ H₄) =
        (L₁ ++ F₁ ++ H₁ ++ (L₂ ++ F₂ ++ H₂) ++ (L₃ ++ F₃ ++ H₃) ++ (L₄ ++ F₄ ++ H₄)) ++ [] ++ [] := by
      simp
    rw [e]
    refine noGap_of_block ?_ ?_ <;> (try simp only [List.forall_mem_append]) <;>
      (try constructorm* _ ∧ _) <;> wclose

end DZZ
end LQGMetric
