/-
# Transport of rooted forests with prescribed terminal matchings

The rooted-forest fiber with matching walks keeps the original edge subsets.
Independent terminal permutations preserve the first-list root range and
reindex the prescribed walks. A vertex equivalence transports the root range
and every walk through the proved vertex transport. Whole signed cardinality
sums follow by permutation reindexing and pointwise subset equivalences.
-/
import LatticeProb.Graph.CopiedGraph.VertexTransport
import LatticeProb.Combinatorics.PairingTransport
import LatticeProb.Combinatorics.TerminalOrder
import Mathlib.Algebra.BigOperators.Ring.Finset



namespace LatticeProb.Graph.CopiedGraph

open LatticeProb.Combinatorics
open scoped Classical BigOperators
noncomputable section

variable {V W E ι : Type*}

/-- The literal original-copy rooted-forest fiber with prescribed matching
walks from `a r` to `b (π r)`. -/
abbrev RootedMatchingForest (J : CopiedGraph V E) (a b : ι → V) (π : Equiv.Perm ι) :=
  {F : Finset E // J.IsRootedForest (Set.range a) F ∧
    ∀ r, J.reaches F (a r) (b (π r))}

/-- **Rooted matching reindexing.** Independent terminal permutations give an
equivalence of the literal rooted matching fibers, fixing every original copy
subset. This does not require either list to be injective. -/
def rootedMatchingReindexEquiv (J : CopiedGraph V E) (a b : ι → V)
    (α β π : Equiv.Perm ι) :
    J.RootedMatchingForest a b π ≃
      J.RootedMatchingForest (a ∘ α) (b ∘ β) (reindexPairing α β π) :=
  Equiv.subtypeEquivRight (fun F => by
    rw [Function.Surjective.range_comp α.surjective a]
    apply and_congr_right
    intro _
    constructor
    · intro h r
      simpa only [Function.comp_apply, reindexPairing_apply, Equiv.apply_symm_apply]
        using h (α r)
    · intro h r
      simpa only [Function.comp_apply, reindexPairing_apply, Equiv.apply_symm_apply]
        using h (α.symm r))

/-- The rooted matching reindexing map preserves the finite copy subset. -/
theorem rootedMatchingReindexEquiv_apply_val (J : CopiedGraph V E) (a b : ι → V)
    (α β π : Equiv.Perm ι) (F : J.RootedMatchingForest a b π) :
    (J.rootedMatchingReindexEquiv a b α β π F).val = F.val := rfl

/-- The inverse rooted matching reindexing also preserves the finite subset. -/
theorem rootedMatchingReindexEquiv_symm_apply_val (J : CopiedGraph V E) (a b : ι → V)
    (α β π : Equiv.Perm ι)
    (F : J.RootedMatchingForest (a ∘ α) (b ∘ β) (reindexPairing α β π)) :
    ((J.rootedMatchingReindexEquiv a b α β π).symm F).val = F.val := rfl

/-- Reindexing both terminal lists preserves each prescribed rooted matching count. -/
theorem card_rootedMatchingForest_reindex (J : CopiedGraph V E) (a b : ι → V)
    (α β π : Equiv.Perm ι) :
    Nat.card (J.RootedMatchingForest (a ∘ α) (b ∘ β) (reindexPairing α β π)) =
      Nat.card (J.RootedMatchingForest a b π) :=
  (Nat.card_congr (J.rootedMatchingReindexEquiv a b α β π)).symm

/-- The signed count of rooted matching forests transforms by the product of
terminal permutation signs, over any commutative coefficient ring. -/
theorem signed_rootedMatchingForest_count_reindex {R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (J : CopiedGraph V E) (a b : ι → V) (α β : Equiv.Perm ι) :
    (∑ π : Equiv.Perm ι, ((Equiv.Perm.sign π : ℤ) : R) *
      (Nat.card (J.RootedMatchingForest (a ∘ α) (b ∘ β) π) : R)) =
    ((Equiv.Perm.sign α : ℤ) : R) * ((Equiv.Perm.sign β : ℤ) : R) *
      (∑ π : Equiv.Perm ι, ((Equiv.Perm.sign π : ℤ) : R) *
        (Nat.card (J.RootedMatchingForest a b π) : R)) := by
  rw [← (reindexPairingEquiv α β).sum_comp]
  simp only [reindexPairingEquiv, Equiv.coe_fn_mk, card_rootedMatchingForest_reindex,
    cast_sign_reindexPairing]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  exact mul_assoc _ _ _

/-- Vertex relabeling induces an identical-subset equivalence of rooted forests
with all prescribed matching walks transported through the actual equivalence. -/
def rootedMatchingRelabelEquiv (J : CopiedGraph V E) (e : V ≃ W) (a b : ι → V)
    (π : Equiv.Perm ι) :
    J.RootedMatchingForest a b π ≃
      (J.relabelVertices e).RootedMatchingForest (e ∘ a) (e ∘ b) π :=
  Equiv.subtypeEquivRight (fun F => by
    rw [Set.range_comp, J.isRootedForest_relabelVertices_iff]
    apply and_congr_right
    intro _
    simp only [Function.comp_apply, J.reaches_relabelVertices_iff e])

/-- Rooted matching vertex transport preserves every original finite subset. -/
theorem rootedMatchingRelabelEquiv_apply_val (J : CopiedGraph V E) (e : V ≃ W)
    (a b : ι → V) (π : Equiv.Perm ι) (F : J.RootedMatchingForest a b π) :
    (J.rootedMatchingRelabelEquiv e a b π F).val = F.val := rfl

/-- The inverse rooted matching vertex transport preserves every finite subset. -/
theorem rootedMatchingRelabelEquiv_symm_apply_val (J : CopiedGraph V E) (e : V ≃ W)
    (a b : ι → V) (π : Equiv.Perm ι)
    (F : (J.relabelVertices e).RootedMatchingForest (e ∘ a) (e ∘ b) π) :
    ((J.rootedMatchingRelabelEquiv e a b π).symm F).val = F.val := rfl

/-- Each rooted matching count is unchanged by vertex relabeling. -/
theorem card_rootedMatchingForest_relabelVertices (J : CopiedGraph V E) (e : V ≃ W)
    (a b : ι → V) (π : Equiv.Perm ι) :
    Nat.card ((J.relabelVertices e).RootedMatchingForest (e ∘ a) (e ∘ b) π) =
      Nat.card (J.RootedMatchingForest a b π) :=
  (Nat.card_congr (J.rootedMatchingRelabelEquiv e a b π)).symm

/-- **Signed rooted matching vertex transport.** The whole signed count is
unchanged by a vertex equivalence, over any commutative ring. -/
theorem signed_rootedMatchingForest_count_relabelVertices {R : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (J : CopiedGraph V E) (e : V ≃ W) (a b : ι → V) :
    (∑ π : Equiv.Perm ι, ((Equiv.Perm.sign π : ℤ) : R) *
      (Nat.card ((J.relabelVertices e).RootedMatchingForest (e ∘ a) (e ∘ b) π) : R)) =
    ∑ π : Equiv.Perm ι, ((Equiv.Perm.sign π : ℤ) : R) *
      (Nat.card (J.RootedMatchingForest a b π) : R) := by
  apply Finset.sum_congr rfl
  intro π _
  rw [J.card_rootedMatchingForest_relabelVertices]

/-- Sorting injective finite terminal lists internally gives the exact rooted
matching signed count, with both produced terminal permutation signs. -/
theorem signed_rootedMatchingForest_count_eq_ordered {R : Type*} [CommRing R]
    [LinearOrder V] {k : ℕ} (J : CopiedGraph V E) (a b : Fin k → V)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    (∑ π : Equiv.Perm (Fin k), ((Equiv.Perm.sign π : ℤ) : R) *
      (Nat.card (J.RootedMatchingForest a b π) : R)) =
    ((Equiv.Perm.sign (terminalOrderPerm a ha) : ℤ) : R) *
      ((Equiv.Perm.sign (terminalOrderPerm b hb) : ℤ) : R) *
      (∑ π : Equiv.Perm (Fin k), ((Equiv.Perm.sign π : ℤ) : R) *
        (Nat.card (J.RootedMatchingForest
          ((Finset.univ.image a).orderEmbOfFin (card_terminal_image a ha))
          ((Finset.univ.image b).orderEmbOfFin (card_terminal_image b hb)) π) : R)) := by
  have h := J.signed_rootedMatchingForest_count_reindex (R := R)
    ((Finset.univ.image a).orderEmbOfFin (card_terminal_image a ha))
    ((Finset.univ.image b).orderEmbOfFin (card_terminal_image b hb))
    (terminalOrderPerm a ha) (terminalOrderPerm b hb)
  rw [← terminal_eq_orderEmbOfFin_comp a ha, ← terminal_eq_orderEmbOfFin_comp b hb] at h
  exact h

end
end LatticeProb.Graph.CopiedGraph
