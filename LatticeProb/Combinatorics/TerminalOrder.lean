module

/-
# Sorting an injective finite terminal list

An injective list is a bijection onto its literal finite image. Composing this
bijection with the inverse increasing enumeration constructs the permutation
of terminal indices. Its evaluation identities relate the original list and
the `orderEmbOfFin` map in both directions, including the empty-list case.
-/
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card

@[expose] public section



namespace LatticeProb.Combinatorics

open scoped Classical
noncomputable section

variable {V : Type*} [LinearOrder V] {k : ℕ}

/-- The finite image of an injective `Fin k` list has cardinality `k`. -/
theorem card_terminal_image (a : Fin k → V) (ha : Function.Injective a) :
    (Finset.univ.image a).card = k := by
  rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]

/-- An injective terminal list is a bijection onto its actual finite image. -/
def terminalImageEquiv (a : Fin k → V) (ha : Function.Injective a) :
    Fin k ≃ (Finset.univ.image a : Finset V) :=
  Equiv.ofBijective (fun r => ⟨a r, Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩⟩)
    ⟨fun _ _ h => ha (congrArg Subtype.val h), fun x => by
      obtain ⟨r, _, hr⟩ := Finset.mem_image.mp x.property
      exact ⟨r, Subtype.ext hr⟩⟩

/-- The permutation taking each original index to its increasing-list rank.
It is constructed from injectivity, with no supplied sorting witness. -/
def terminalOrderPerm (a : Fin k → V) (ha : Function.Injective a) : Equiv.Perm (Fin k) :=
  (terminalImageEquiv a ha).trans
    ((Finset.univ.image a).orderIsoOfFin (card_terminal_image a ha)).toEquiv.symm

/-- Increasing enumeration at the produced rank recovers the original terminal. -/
theorem orderEmbOfFin_terminalOrderPerm (a : Fin k → V) (ha : Function.Injective a)
    (r : Fin k) :
    (Finset.univ.image a).orderEmbOfFin (card_terminal_image a ha)
      (terminalOrderPerm a ha r) = a r := by
  rw [← Finset.coe_orderIsoOfFin_apply]
  change (((Finset.univ.image a).orderIsoOfFin (card_terminal_image a ha))
    (((Finset.univ.image a).orderIsoOfFin (card_terminal_image a ha)).symm
      (terminalImageEquiv a ha r))).val = a r
  rw [OrderIso.apply_symm_apply]
  rfl

/-- The original terminal list is the increasing image enumeration composed
with its produced index permutation. -/
theorem terminal_eq_orderEmbOfFin_comp (a : Fin k → V) (ha : Function.Injective a) :
    a = (Finset.univ.image a).orderEmbOfFin (card_terminal_image a ha) ∘
      terminalOrderPerm a ha :=
  funext (fun r => (orderEmbOfFin_terminalOrderPerm a ha r).symm)

/-- The inverse produced permutation sorts the original terminal list exactly. -/
theorem orderEmbOfFin_eq_terminal_comp_symm (a : Fin k → V) (ha : Function.Injective a) :
    ((Finset.univ.image a).orderEmbOfFin (card_terminal_image a ha) : Fin k → V) =
      a ∘ (terminalOrderPerm a ha).symm := by
  funext r
  have h := orderEmbOfFin_terminalOrderPerm a ha ((terminalOrderPerm a ha).symm r)
  simpa only [Equiv.apply_symm_apply, Function.comp_apply] using h

/-- **Produced sorting witness.** Every injective terminal list admits an
internally constructed permutation whose reindexing is its increasing finite
image enumeration. No positivity or nonempty-carrier premise is needed. -/
theorem exists_terminal_sorting_perm (a : Fin k → V) (ha : Function.Injective a) :
    ∃ α : Equiv.Perm (Fin k), a ∘ α =
      (Finset.univ.image a).orderEmbOfFin (card_terminal_image a ha) :=
  ⟨(terminalOrderPerm a ha).symm, (orderEmbOfFin_eq_terminal_comp_symm a ha).symm⟩

end
end LatticeProb.Combinatorics
