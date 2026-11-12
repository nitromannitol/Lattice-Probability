/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12X10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X9

/-!
# DZZ Lemma 3.12: the walk along one side (D93 §2, packet P-6a, coarse step)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 3.12 (l. 1471–1477),
ring form of DEC-93 §2: the part of the closed walk along one side, from the meeting point `u`
with the previous side to the meeting point `v` with the next side, through the whole cut
crossing `L ++ F ++ H` (S3L12X4/X5), keeps the three parts in order (`spur_walk`).

* **`side_walk`**.

Own elementary arguments, DV-D93.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DZZ

lemma side_walk_aux {α : Type*} {r : α → α → Prop} (hs : ∀ x y, r x y → r y x) {Y : List α}
    (hY : Y.IsChain r) {Y₁ Y₂ Z₁ Z₂ : List α} {u v : α} (e₁ : Y = Y₁ ++ u :: Y₂)
    (e₂ : Y = Z₁ ++ v :: Z₂) {L' F' H' : List α}
    (eS : (Y₁ ++ [u]).reverse ++ Y ++ (v :: Z₂).reverse = L' ++ F' ++ H') :
    (L' ++ F' ++ H').IsChain (EqOr r) ∧ (L' ++ F' ++ H').head? = some u ∧
      (L' ++ F' ++ H').getLast? = some v ∧ ∀ x, x ∈ L' ++ F' ++ H' ↔ x ∈ Y := by
  rw [← eS]; exact spur_walk hs hY e₁ e₂

/-- **The walk along one side**, with its low-corner, middle and high-corner parts. -/
theorem side_walk {α : Type*} {r : α → α → Prop} (hs : ∀ x y, r x y → r y x)
    {L F H : List α} (hY : (L ++ F ++ H).IsChain r) {u v : α}
    (hu : u ∈ L ∨ (L = [] ∧ u ∈ F)) (hv : v ∈ H ∨ (H = [] ∧ v ∈ F)) :
    ∃ L' F' H' : List α, (L' ++ F' ++ H').IsChain (EqOr r) ∧ (L' ++ F' ++ H').head? = some u ∧
      (L' ++ F' ++ H').getLast? = some v ∧ (∀ x, x ∈ L' ++ F' ++ H' ↔ x ∈ L ++ F ++ H) ∧
      (∀ x ∈ L', x ∈ L) ∧ (∀ x ∈ F', x ∈ F) ∧ (∀ x ∈ H', x ∈ H) := by
  rcases hu with hu | ⟨rfl, hu⟩ <;> rcases hv with hv | ⟨rfl, hv⟩
  · obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hu
    obtain ⟨H₁, H₂, rfl⟩ := List.append_of_mem hv
    obtain ⟨h1, h2, h3, h4⟩ := side_walk_aux (u := u) (v := v) (Y₁ := L₁) (Y₂ := L₂ ++ F ++ (H₁ ++ v :: H₂))
      (Z₁ := L₁ ++ u :: L₂ ++ F ++ H₁) (Z₂ := H₂)
      (L' := (L₁ ++ [u]).reverse ++ (L₁ ++ u :: L₂)) (F' := F)
      (H' := (H₁ ++ v :: H₂) ++ (v :: H₂).reverse) hs hY (by simp) (by simp) (by simp)
    refine ⟨_, _, _, h1, h2, h3, h4, ?_, fun x hx => hx, ?_⟩
    · intro x hx; simp only [List.mem_append, List.mem_reverse, List.mem_singleton,
        List.mem_cons] at hx ⊢; tauto
    · intro x hx; simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hx ⊢; tauto
  · obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hu
    obtain ⟨F₁, F₂, rfl⟩ := List.append_of_mem hv
    obtain ⟨h1, h2, h3, h4⟩ := side_walk_aux (u := u) (v := v) (Y₁ := L₁) (Y₂ := L₂ ++ (F₁ ++ v :: F₂) ++ [])
      (Z₁ := L₁ ++ u :: L₂ ++ F₁) (Z₂ := F₂)
      (L' := (L₁ ++ [u]).reverse ++ (L₁ ++ u :: L₂)) (F' := (F₁ ++ v :: F₂) ++ (v :: F₂).reverse)
      (H' := []) hs hY (by simp) (by simp) (by simp)
    refine ⟨_, _, _, h1, h2, h3, h4, ?_, ?_, fun x hx => by simp at hx⟩
    · intro x hx; simp only [List.mem_append, List.mem_reverse, List.mem_singleton,
        List.mem_cons] at hx ⊢; tauto
    · intro x hx; simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hx ⊢; tauto
  · obtain ⟨F₁, F₂, rfl⟩ := List.append_of_mem hu
    obtain ⟨H₁, H₂, rfl⟩ := List.append_of_mem hv
    obtain ⟨h1, h2, h3, h4⟩ := side_walk_aux (u := u) (v := v) (Y₁ := F₁) (Y₂ := F₂ ++ (H₁ ++ v :: H₂))
      (Z₁ := F₁ ++ u :: F₂ ++ H₁) (Z₂ := H₂)
      (L' := []) (F' := (F₁ ++ [u]).reverse ++ (F₁ ++ u :: F₂))
      (H' := (H₁ ++ v :: H₂) ++ (v :: H₂).reverse) hs hY (by simp) (by simp) (by simp)
    refine ⟨_, _, _, h1, h2, h3, h4, fun x hx => by simp at hx, ?_, ?_⟩
    · intro x hx; simp only [List.mem_append, List.mem_reverse, List.mem_singleton,
        List.mem_cons] at hx ⊢; tauto
    · intro x hx; simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hx ⊢; tauto
  · obtain ⟨F₁, F₂, eF⟩ := List.append_of_mem hu
    obtain ⟨G₁, G₂, eG⟩ := List.append_of_mem hv
    have hY' := hY
    obtain ⟨h1, h2, h3, h4⟩ := side_walk_aux (u := u) (v := v) (Y₁ := F₁) (Y₂ := F₂) (Z₁ := G₁) (Z₂ := G₂)
      (L' := []) (F' := (F₁ ++ [u]).reverse ++ F ++ (v :: G₂).reverse) (H' := [])
      hs hY (by rw [eF]; simp) (by rw [eG]; simp) (by simp)
    refine ⟨_, _, _, h1, h2, h3, h4, fun x hx => by simp at hx, ?_, fun x hx => by simp at hx⟩
    intro x hx
    simp only [List.append_nil, List.mem_append, List.mem_reverse, List.mem_singleton,
      List.mem_cons] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · rw [eF]; simp only [List.mem_append, List.mem_cons]; tauto
    · rw [eF]; simp only [List.mem_append, List.mem_cons]; simp at hx; tauto
    · exact hx
    · rw [eG]; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto

end DZZ
end LQGMetric
