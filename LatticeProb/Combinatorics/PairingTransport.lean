module

/-
# Reindexing paired terminal lists

Changing the first and second terminal indices by `α` and `β` changes the
matching permutation `π` to `β.symm ∘ π ∘ α`. The coverage, cross-matching,
and first-list separation predicates are transported by their actual index
witnesses. The permutation equivalence also gives the exact product of signs.
-/
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section



namespace LatticeProb.Combinatorics

variable {ι V : Type*}

/-- The matching obtained after reindexing the first list by `α` and the
second list by `β`: its value at `r` is `β.symm (π (α r))`. -/
def reindexPairing (α β π : Equiv.Perm ι) : Equiv.Perm ι :=
  (α.trans π).trans β.symm

/-- Evaluation of the reindexed matching on an actual terminal index. -/
theorem reindexPairing_apply (α β π : Equiv.Perm ι) (r : ι) :
    reindexPairing α β π r = β.symm (π (α r)) := rfl

/-- Reindexing matchings is a bijection of the whole permutation carrier. -/
def reindexPairingEquiv (α β : Equiv.Perm ι) : Equiv.Perm ι ≃ Equiv.Perm ι where
  toFun := reindexPairing α β
  invFun := reindexPairing α.symm β.symm
  left_inv π := by
    ext r
    simp only [reindexPairing_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  right_inv π := by
    ext r
    simp only [reindexPairing_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

/-- The sign of a reindexed matching is the product of the two terminal
permutation signs and the original matching sign. -/
theorem sign_reindexPairing [Fintype ι] [DecidableEq ι]
    (α β π : Equiv.Perm ι) :
    Equiv.Perm.sign (reindexPairing α β π) =
      Equiv.Perm.sign α * Equiv.Perm.sign β * Equiv.Perm.sign π := by
  rw [reindexPairing, Equiv.Perm.sign_trans, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_symm]
  rw [mul_comm (Equiv.Perm.sign π) (Equiv.Perm.sign α), ← mul_assoc,
    mul_comm (Equiv.Perm.sign β) (Equiv.Perm.sign α)]

/-- The exact sign product, cast through integers into any commutative ring. -/
theorem cast_sign_reindexPairing {R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (α β π : Equiv.Perm ι) :
    ((Equiv.Perm.sign (reindexPairing α β π) : ℤ) : R) =
      ((Equiv.Perm.sign α : ℤ) : R) * ((Equiv.Perm.sign β : ℤ) : R) *
        ((Equiv.Perm.sign π : ℤ) : R) := by
  rw [sign_reindexPairing]
  simp only [Units.val_mul, Int.cast_mul]

/-- **Paired terminal reindexing.** Coverage by either terminal list, exact
cross connectivity and distinct first-list separation are invariant under
independent terminal permutations. This holds for any binary relation,
including copied-walk reachability, without injectivity or nonempty carriers. -/
theorem pairing_reindex_iff (reach : V → V → Prop) (a b : ι → V)
    (α β π : Equiv.Perm ι) :
    ((∀ y, ∃ r, reach y (a (α r)) ∨ reach y (b (β r))) ∧
      (∀ r s, reach (a (α r)) (b (β s)) ↔ s = reindexPairing α β π r) ∧
      (∀ r s, r ≠ s → ¬reach (a (α r)) (a (α s)))) ↔
    ((∀ y, ∃ r, reach y (a r) ∨ reach y (b r)) ∧
      (∀ r s, reach (a r) (b s) ↔ s = π r) ∧
      (∀ r s, r ≠ s → ¬reach (a r) (a s))) := by
  constructor
  · rintro ⟨hc, hm, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨r, hr | hr⟩ := hc y
      · exact ⟨α r, Or.inl hr⟩
      · exact ⟨β r, Or.inr hr⟩
    · intro r s
      have h := hm (α.symm r) (β.symm s)
      simpa only [Equiv.apply_symm_apply, reindexPairing_apply,
        Equiv.symm_apply_eq, Equiv.apply_symm_apply] using h
    · intro r s hne
      have hne' : α.symm r ≠ α.symm s := fun h => hne (α.symm.injective h)
      simpa only [Equiv.apply_symm_apply] using hs (α.symm r) (α.symm s) hne'
  · rintro ⟨hc, hm, hs⟩
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨r, hr | hr⟩ := hc y
      · exact ⟨α.symm r, Or.inl (by simpa only [Equiv.apply_symm_apply] using hr)⟩
      · exact ⟨β.symm r, Or.inr (by simpa only [Equiv.apply_symm_apply] using hr)⟩
    · intro r s
      simpa only [reindexPairing_apply, Equiv.eq_symm_apply] using hm (α r) (β s)
    · intro r s hne
      exact hs (α r) (α s) (fun h => hne (α.injective h))

end LatticeProb.Combinatorics
