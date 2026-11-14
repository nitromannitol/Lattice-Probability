import Mathlib.Data.Set.Countable

/-!
# Countable exceptional pairs

A pair of relations with countable fibers produces only countably many pairs
involving endpoints from countable exceptional sets.
-/

open Set

namespace LatticeProb

/-- If two relations have countable fibers in both directions, the pairs formed
from a common source and either target are countable when one of the targets
belongs to a countable exceptional set. -/
theorem countable_exceptional_relation_pairs {α : Type*} (R S : α → α → Prop)
    (E F : Set α) (hE : E.Countable) (hF : F.Countable)
    (hR : ∀ x, {y | R x y}.Countable) (hS : ∀ x, {y | S x y}.Countable)
    (hR' : ∀ y, {x | R x y}.Countable) (hS' : ∀ y, {x | S x y}.Countable) :
    {p : α × α | ∃ a b, R p.1 a ∧ S p.1 b ∧ (a ∈ E ∨ b ∈ F) ∧
      (p.2 = p.1 ∨ p.2 = a ∨ p.2 = b)}.Countable := by
  let A : Set α := (⋃ a ∈ E, {x | R x a}) ∪ ⋃ b ∈ F, {x | S x b}
  have hA : A.Countable := (hE.biUnion fun a _ => hR' a).union
    (hF.biUnion fun b _ => hS' b)
  let B : α → Set α := fun x => {x} ∪ {y | R x y} ∪ {y | S x y}
  have hB (x : α) : (B x).Countable := ((countable_singleton x).union (hR x)).union (hS x)
  have hcover : {p : α × α | ∃ a b, R p.1 a ∧ S p.1 b ∧ (a ∈ E ∨ b ∈ F) ∧
      (p.2 = p.1 ∨ p.2 = a ∨ p.2 = b)} ⊆
      ⋃ x ∈ A, (fun y => (x, y)) '' B x := by
    rintro ⟨x, y⟩ ⟨a, b, hra, hsb, hab, hy⟩
    have hx : x ∈ A := by
      rcases hab with ha | hb
      · exact Or.inl (mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, hra⟩⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hb, hsb⟩⟩)
    refine mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, ?_⟩⟩
    refine ⟨y, ?_, rfl⟩
    change y = x ∨ y = a ∨ y = b at hy
    rcases hy with rfl | rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr hra)
    · exact Or.inr hsb
  exact (hA.biUnion fun x _ => (hB x).image _).mono hcover

end LatticeProb
