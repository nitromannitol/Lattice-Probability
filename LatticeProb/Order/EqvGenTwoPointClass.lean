import Mathlib.Logic.Relation
import Mathlib.Order.Basic

/-!
# Two-point classes of a generated equivalence relation

Let `r` be a relation and `Relation.EqvGen r` the equivalence relation it generates. A chain of `r`-steps (in either
direction) starting at `s` stays inside the equivalence class of `s`. Consequently, if the class of `s` is contained
in `{s, t}` with `s ≠ t` and `s` is equivalent to `t`, then `s` and `t` are related by a single step of `r`, in one of
the two directions.
-/

set_option autoImplicit false

namespace LatticeProb.Relation

variable {α : Type*} {r : α → α → Prop}

/-- If the class of `s` under `Relation.EqvGen r` is contained in `{s, t}` and there is no direct `r`-step between `s`
and `t`, then an `EqvGen r`-chain whose left end is in the class of `s` either stays at `s` or never visits `s`. -/
theorem eqvGen_eq_iff_eq_of_class_subset_pair {s t : α}
    (hcls : ∀ u, Relation.EqvGen r s u → u = s ∨ u = t) (hst : ¬ r s t) (hts : ¬ r t s)
    {a b : α} (hab : Relation.EqvGen r a b) : Relation.EqvGen r s a → (a = s ↔ b = s) := by
  induction hab with
  | rel x y hxy =>
    intro hsx
    have hsy : Relation.EqvGen r s y := Relation.EqvGen.trans s x y hsx (Relation.EqvGen.rel x y hxy)
    rcases hcls x hsx with hx | hx <;> rcases hcls y hsy with hy | hy
    · rw [hx, hy]
    · rw [hx, hy] at hxy
      exact absurd hxy hst
    · rw [hx, hy] at hxy
      exact absurd hxy hts
    · rw [hx, hy]
  | refl x => exact fun _ => Iff.rfl
  | symm x y hxy ih =>
    intro hsy
    exact (ih (Relation.EqvGen.trans s y x hsy (Relation.EqvGen.symm x y hxy))).symm
  | trans x y z hxy _ ih₁ ih₂ =>
    intro hsx
    exact (ih₁ hsx).trans (ih₂ (Relation.EqvGen.trans s x y hsx hxy))

/-- **Two-point classes are direct steps.** If `s ≠ t` are equivalent under `Relation.EqvGen r` and the class of `s`
is contained in `{s, t}`, then `r s t` or `r t s`. -/
theorem rel_or_rel_of_eqvGen_of_class_subset_pair {s t : α} (hne : s ≠ t) (h : Relation.EqvGen r s t)
    (hcls : ∀ u, Relation.EqvGen r s u → u = s ∨ u = t) : r s t ∨ r t s := by
  by_cases h₁ : r s t
  · exact Or.inl h₁
  by_cases h₂ : r t s
  · exact Or.inr h₂
  have key := eqvGen_eq_iff_eq_of_class_subset_pair hcls h₁ h₂ h (Relation.EqvGen.refl s)
  exact absurd (key.mp rfl).symm hne

/-- Version for a strict relation: if `r` only relates `a` to `b` when `a < b`, a two-point class `{s, t}` with
`s < t` is a direct step `r s t`. -/
theorem rel_of_eqvGen_of_class_subset_pair {β : Type*} [Preorder β] {r : β → β → Prop}
    (hr : ∀ a b, r a b → a < b) {s t : β} (hlt : s < t) (h : Relation.EqvGen r s t)
    (hcls : ∀ u, Relation.EqvGen r s u → u = s ∨ u = t) : r s t := by
  rcases rel_or_rel_of_eqvGen_of_class_subset_pair hlt.ne h hcls with h' | h'
  · exact h'
  · exact absurd (hr t s h') (not_lt_of_gt hlt)

end LatticeProb.Relation
