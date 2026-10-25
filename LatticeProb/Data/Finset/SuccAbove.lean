module

/-
Finite ordered sets after deleting a position from a finite ordinal.
-/

public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section



namespace Finset
open scoped BigOperators
variable {n k d : ℕ}

/-- Pull back a finite set along the increasing embedding omitting `r`. -/
def preimageSuccAbove (I : Finset (Fin (n + 1))) (r : Fin (n + 1)) : Finset (Fin n) :=
  univ.filter (fun x => r.succAbove x ∈ I)

/-- Membership in the pullback is literal membership after the omitted-position embedding. -/
@[simp]
theorem mem_preimageSuccAbove (I : Finset (Fin (n + 1))) (r : Fin (n + 1)) (x : Fin n) :
    x ∈ I.preimageSuccAbove r ↔ r.succAbove x ∈ I := by
  simp only [preimageSuccAbove, mem_filter, mem_univ, true_and]

/-- Mapping the pullback back to the original ordinal deletes precisely the omitted position. -/
theorem map_preimageSuccAbove (I : Finset (Fin (n + 1))) (r : Fin (n + 1)) :
    (I.preimageSuccAbove r).map (Fin.succAboveOrderEmb r).toEmbedding = I.erase r := by
  ext x
  simp only [mem_map, mem_erase, mem_preimageSuccAbove, Fin.succAboveOrderEmb]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Fin.succAbove_ne _ _, ha⟩
  · rintro ⟨hxr, hx⟩
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hxr
    exact ⟨a, hx, rfl⟩

/-- Deleting a member reduces the cardinality by one. -/
theorem card_preimageSuccAbove (I : Finset (Fin (n + 1))) (r : Fin (n + 1))
    (hr : r ∈ I) : (I.preimageSuccAbove r).card = I.card - 1 := by
  rw [← card_map (Fin.succAboveOrderEmb r).toEmbedding, map_preimageSuccAbove,
    card_erase_of_mem hr]

/-- Increasing complementary enumerations commute with deletion of a root position. -/
theorem orderEmbOfFin_preimageSuccAbove_compl
    (I : Finset (Fin (n + 1))) (r : Fin (n + 1))
    (hI : Iᶜ.card = d) (hJ : (I.preimageSuccAbove r)ᶜ.card = d) (a : Fin d) :
    r.succAbove ((I.preimageSuccAbove r)ᶜ.orderEmbOfFin hJ a) =
      Iᶜ.orderEmbOfFin hI a := by
  have h := orderEmbOfFin_unique hI
    (f := fun a => r.succAbove ((I.preimageSuccAbove r)ᶜ.orderEmbOfFin hJ a))
    (fun a => by
      have hm := orderEmbOfFin_mem (I.preimageSuccAbove r)ᶜ hJ a
      simpa only [mem_compl, mem_preimageSuccAbove] using hm)
    ((Fin.strictMono_succAbove r).comp ((I.preimageSuccAbove r)ᶜ.orderEmbOfFin hJ).strictMono)
  exact congrFun h a

/-- Deleting the final member of an increasing enumeration retains its preceding entries. -/
theorem orderEmbOfFin_preimageSuccAbove
    (I : Finset (Fin (n + 1))) (hI : I.card = k + 1) (r : Fin (n + 1))
    (hr : r = I.orderEmbOfFin hI (Fin.last k))
    (hJ : (I.preimageSuccAbove r).card = k) (j : Fin k) :
    r.succAbove ((I.preimageSuccAbove r).orderEmbOfFin hJ j) =
      I.orderEmbOfFin hI j.castSucc := by
  have hrmem : r ∈ I := hr ▸ orderEmbOfFin_mem I hI (Fin.last k)
  have he : (I.erase r).card = k := by
    rw [card_erase_of_mem hrmem, hI, Nat.add_sub_cancel]
  have hleft := orderEmbOfFin_unique he
    (f := fun j => r.succAbove ((I.preimageSuccAbove r).orderEmbOfFin hJ j))
    (fun j => by
      exact mem_erase.mpr ⟨Fin.succAbove_ne _ _,
        (mem_preimageSuccAbove I r _).mp (orderEmbOfFin_mem _ hJ j)⟩)
    ((Fin.strictMono_succAbove r).comp ((I.preimageSuccAbove r).orderEmbOfFin hJ).strictMono)
  have hright := orderEmbOfFin_unique he
    (f := fun j : Fin k => I.orderEmbOfFin hI j.castSucc)
    (fun j => by
      refine mem_erase.mpr ⟨?_, orderEmbOfFin_mem I hI j.castSucc⟩
      rw [hr]
      exact (I.orderEmbOfFin hI).injective.ne (Fin.castSucc_ne_last j))
    ((I.orderEmbOfFin hI).strictMono.comp Fin.strictMono_castSucc)
  exact congrFun (hleft.trans hright.symm) j

/-- **Removing an ordered finite index.** The sum of numeric labels loses precisely the largest deleted label. -/
theorem sum_val_preimageSuccAbove
    (I : Finset (Fin (n + 1))) (r : Fin (n + 1)) (hr : r ∈ I)
    (hmax : ∀ x ∈ I, x ≤ r) :
    (∑ x ∈ I, (x : ℕ)) = (∑ x ∈ I.preimageSuccAbove r, (x : ℕ)) + (r : ℕ) := by
  rw [← sum_erase_add I (fun x => (x : ℕ)) hr, ← map_preimageSuccAbove I r, sum_map]
  congr 1
  apply sum_congr rfl
  intro x hx
  have hlt : r.succAbove x < r :=
    lt_of_le_of_ne (hmax _ ((mem_preimageSuccAbove I r x).mp hx)) (Fin.succAbove_ne _ _)
  change (r.succAbove x : ℕ) = (x : ℕ)
  rw [Fin.succAbove_of_castSucc_lt _ _ ((Fin.succAbove_lt_iff_castSucc_lt _ _).mp hlt)]
  rfl

end Finset
