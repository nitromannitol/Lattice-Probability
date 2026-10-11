/-
Finite copied-forest sums are partitioned by their unique component root matching.
The private dependent-sum reduction follows `Fintype.prod_dite` in Mathlib.
For that adapted reduction:
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeProb.Graph.CopiedGraph.RootMatching
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Sigma.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting copied forests by their component root matching

The unique component correspondence partitions forests rooted at two enumerated
root sets into permutation fibers. Reindexing a finite weighted sum through this
partition gives the weight of each permutation times its exact fiber cardinality.
-/

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical BigOperators
noncomputable section
variable {V E ι : Type*} {G : CopiedGraph V E} {R S : Set V} {F : Finset E}

/-- A component-preserving permutation of two root enumerations gives rootedness
at the second root set. -/
theorem IsRootedForest.of_perm (hR : G.IsRootedForest R F)
    (i : ι ≃ R) (j : ι ≃ S) (π : Equiv.Perm ι)
    (hπ : ∀ a, G.reaches F (i a).val (j (π a)).val) :
    G.IsRootedForest S F := by
  apply hR.of_rootEquiv ((i.symm.trans π).trans j)
  intro r
  simpa only [Equiv.trans_apply, i.apply_symm_apply] using hπ (i.symm r)

/-- The unique permutation pairing enumerated roots in the same component of a
forest rooted at both sets. -/
def rootMatchingPerm (i : ι ≃ R) (j : ι ≃ S)
    (hR : G.IsRootedForest R F) (hS : G.IsRootedForest S F) : Equiv.Perm ι :=
  ((hR.iff_existsUnique_perm i j).mp hS).choose

/-- The root matching permutation connects each first root to its paired second root. -/
theorem rootMatchingPerm_reaches (i : ι ≃ R) (j : ι ≃ S)
    (hR : G.IsRootedForest R F) (hS : G.IsRootedForest S F) (a : ι) :
    G.reaches F (i a).val (j (rootMatchingPerm i j hR hS a)).val :=
  ((hR.iff_existsUnique_perm i j).mp hS).choose_spec.1 a

/-- A permutation is the chosen root matching exactly when all its pairs are connected. -/
theorem rootMatchingPerm_eq_iff (i : ι ≃ R) (j : ι ≃ S)
    (hR : G.IsRootedForest R F) (hS : G.IsRootedForest S F) (π : Equiv.Perm ι) :
    rootMatchingPerm i j hR hS = π ↔
      ∀ a, G.reaches F (i a).val (j (π a)).val := by
  constructor
  · rintro rfl
    exact rootMatchingPerm_reaches i j hR hS
  · intro hπ
    exact (((hR.iff_existsUnique_perm i j).mp hS).choose_spec.2 π hπ).symm

/-- Forests rooted at both sets are equivalent to their disjoint permutation
fibers; the selected original edge-copy set is unchanged in either direction. -/
def rootedForestEquivMatchingPerm (G : CopiedGraph V E) (i : ι ≃ R) (j : ι ≃ S) :
    {F : Finset E // G.IsRootedForest R F ∧ G.IsRootedForest S F} ≃
      Σ π : Equiv.Perm ι, {F : Finset E // G.IsRootedForest R F ∧
        ∀ a, G.reaches F (i a).val (j (π a)).val} := by
  let f : {F : Finset E // G.IsRootedForest R F ∧ G.IsRootedForest S F} →
      Σ π : Equiv.Perm ι, {F : Finset E // G.IsRootedForest R F ∧
        ∀ a, G.reaches F (i a).val (j (π a)).val} := fun F =>
    ⟨rootMatchingPerm i j F.property.1 F.property.2,
      F.val, F.property.1, rootMatchingPerm_reaches i j F.property.1 F.property.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro A B h
    exact Subtype.ext (congrArg (fun x => x.2.val) h)
  · rintro ⟨π, F⟩
    have hS := F.property.1.of_perm i j π F.property.2
    refine ⟨⟨F.val, F.property.1, hS⟩, ?_⟩
    have hπ := (rootMatchingPerm_eq_iff i j F.property.1 hS π).mpr F.property.2
    dsimp only [f]
    exact Sigma.subtype_ext hπ rfl

/-- The forward partition map retains every selected original copy. -/
theorem rootedForestEquivMatchingPerm_val (G : CopiedGraph V E) (i : ι ≃ R) (j : ι ≃ S)
    (F : {F : Finset E // G.IsRootedForest R F ∧ G.IsRootedForest S F}) :
    (rootedForestEquivMatchingPerm G i j F).2.val = F.val := rfl

/-- The first coordinate of the partition is the unique component root matching. -/
theorem rootedForestEquivMatchingPerm_fst (G : CopiedGraph V E) (i : ι ≃ R) (j : ι ≃ S)
    (F : {F : Finset E // G.IsRootedForest R F ∧ G.IsRootedForest S F}) :
    (rootedForestEquivMatchingPerm G i j F).1 =
      rootMatchingPerm i j F.property.1 F.property.2 := rfl

/-- On an exact matching fiber, every forest has the specified permutation, so
the weighted fiber sum is its cardinality times that permutation's weight.
Second-rootedness is constructed from each member's actual matching walks. -/
theorem sum_rootMatchingPerm_fiber_eq [Fintype E] {A : Type*} [Semiring A]
    (G : CopiedGraph V E) (i : ι ≃ R) (j : ι ≃ S) (w : Equiv.Perm ι → A)
    (π : Equiv.Perm ι) :
    (∑ F : {F : Finset E // G.IsRootedForest R F ∧
        ∀ a, G.reaches F (i a).val (j (π a)).val},
      w (rootMatchingPerm i j F.property.1
        (F.property.1.of_perm i j π F.property.2))) =
      w π * (Nat.card {F : Finset E // G.IsRootedForest R F ∧
        ∀ a, G.reaches F (i a).val (j (π a)).val} : A) := by
  calc
    _ = ∑ _F : {F : Finset E // G.IsRootedForest R F ∧
        ∀ a, G.reaches F (i a).val (j (π a)).val}, w π := by
      apply Finset.sum_congr rfl
      intro F _
      rw [(rootMatchingPerm_eq_iff i j F.property.1
        (F.property.1.of_perm i j π F.property.2) π).mpr F.property.2]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul']

/-- **Counting by root matching.** A weighted sum over forests rooted at both sets
is the sum of each permutation weight times the number of its exact matching forests. -/
theorem sum_rootMatchingPerm_eq [Fintype E] [Fintype ι] [DecidableEq ι] {A : Type*} [Semiring A]
    (G : CopiedGraph V E) (i : ι ≃ R) (j : ι ≃ S) (w : Equiv.Perm ι → A) :
    (∑ F : {F : Finset E // G.IsRootedForest R F ∧ G.IsRootedForest S F},
      w (rootMatchingPerm i j F.property.1 F.property.2)) =
      ∑ π : Equiv.Perm ι, w π *
        (Nat.card {F : Finset E // G.IsRootedForest R F ∧
          ∀ a, G.reaches F (i a).val (j (π a)).val} : A) := by
  calc
    _ = ∑ T : (Σ π : Equiv.Perm ι, {F : Finset E // G.IsRootedForest R F ∧
        ∀ a, G.reaches F (i a).val (j (π a)).val}), w T.1 :=
      Fintype.sum_equiv (rootedForestEquivMatchingPerm G i j) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro π _
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
        nsmul_eq_mul']

/-- Forgetting the edge-count restriction on a doubly rooted forest is an
equivalence: its size is already forced by rootedness at the first finite root set. -/
def sizedRootedForestEquiv [Fintype V] (G : CopiedGraph V E)
    (R : Finset V) (S : Set V) :
    {F : {F : Finset E // F.card = Fintype.card V - R.card} //
      G.IsRootedForest (R : Set V) F.val ∧ G.IsRootedForest S F.val} ≃
    {F : Finset E // G.IsRootedForest (R : Set V) F ∧ G.IsRootedForest S F} where
  toFun F := ⟨F.val.val, F.property⟩
  invFun F := ⟨⟨F.val, by
    have hc := F.property.1.card_add_card_roots
    rw [← hc, Nat.add_sub_cancel]⟩, F.property⟩
  left_inv F := Subtype.ext (Subtype.ext rfl)
  right_inv F := Subtype.ext rfl

/-- The size-forgetting equivalence keeps the original selected copies. -/
theorem sizedRootedForestEquiv_val [Fintype V] (G : CopiedGraph V E)
    (R : Finset V) (S : Set V)
    (F : {F : {F : Finset E // F.card = Fintype.card V - R.card} //
      G.IsRootedForest (R : Set V) F.val ∧ G.IsRootedForest S F.val}) :
    (sizedRootedForestEquiv G R S F).val = F.val.val := rfl

private theorem sum_dite_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : ∀ a, p a → M) :
    (∑ a, if h : p a then f a h else 0) = ∑ a : {a // p a}, f a.val a.property := by
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  let e : {a : α // a ∈ Finset.univ.filter p} ≃ {a : α // p a} :=
    Equiv.subtypeEquivRight (fun _ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The finite sum over selections of the forced size, with zero for selections
not rooted at both sets, equals the exact weighted permutation-fiber count. -/
theorem sum_rootMatchingPerm_of_card_sub_eq [Fintype V] [Fintype E] [Fintype ι] [DecidableEq ι]
    {A : Type*} [Semiring A] (G : CopiedGraph V E) (R : Finset V) (S : Set V)
    (i : ι ≃ (R : Set V)) (j : ι ≃ S) (w : Equiv.Perm ι → A) :
    (∑ F : {F : Finset E // F.card = Fintype.card V - R.card},
      if h : G.IsRootedForest (R : Set V) F.val ∧ G.IsRootedForest S F.val then
        w (rootMatchingPerm i j h.1 h.2) else 0) =
      ∑ π : Equiv.Perm ι, w π *
        (Nat.card {F : Finset E // G.IsRootedForest (R : Set V) F ∧
          ∀ a, G.reaches F (i a).val (j (π a)).val} : A) := by
  rw [sum_dite_zero]
  calc
    _ = ∑ F : {F : Finset E //
        G.IsRootedForest (R : Set V) F ∧ G.IsRootedForest S F},
        w (rootMatchingPerm i j F.property.1 F.property.2) :=
      Fintype.sum_equiv (sizedRootedForestEquiv G R S) _ _ (fun _ => rfl)
    _ = _ := sum_rootMatchingPerm_eq G i j w

/-- Reindex selections of size m when m is the vertex count minus the root count.
The numerical equality only identifies the chosen size; rootedness and matching
are proved within the partition, not supplied as premises. -/
theorem sum_rootMatchingPerm_of_card_eq [Fintype V] [Fintype E] [Fintype ι] [DecidableEq ι]
    {A : Type*} [Semiring A] (G : CopiedGraph V E) (R : Finset V) (S : Set V)
    (i : ι ≃ (R : Set V)) (j : ι ≃ S) (w : Equiv.Perm ι → A)
    (m : ℕ) (hm : Fintype.card V - R.card = m) :
    (∑ F : {F : Finset E // F.card = m},
      if h : G.IsRootedForest (R : Set V) F.val ∧ G.IsRootedForest S F.val then
        w (rootMatchingPerm i j h.1 h.2) else 0) =
      ∑ π : Equiv.Perm ι, w π *
        (Nat.card {F : Finset E // G.IsRootedForest (R : Set V) F ∧
          ∀ a, G.reaches F (i a).val (j (π a)).val} : A) := by
  subst m
  exact sum_rootMatchingPerm_of_card_sub_eq G R S i j w

end
end LatticeProb.Graph.CopiedGraph
