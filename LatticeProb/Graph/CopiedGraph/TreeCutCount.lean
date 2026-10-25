module

/-
Weighted same-copy tree cuts and literal two-root forest counts.
No connectivity, planarity, determinant identity, or electrical solver is assumed.
-/
public import LatticeProb.Graph.CopiedGraph.TreeCut
public import LatticeProb.Graph.CopiedGraph.SignedPathTraversal
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*}

/-- The literal cardinality of two-root forests connecting the given vertex to
 the first root; no normalization by the number of forests is performed. -/
def forestColorCount (J : CopiedGraph V E) (u v x : V) : ℕ :=
  Nat.card {F : J.TwoRootForest u v // J.reaches F.val x u}

/-- The weight of a tree cut is the difference of its forest endpoint colors,
with the sign determined by the stored orientation of the same original copy. -/
theorem signedPathTraversal_treeCutEquiv (J : CopiedGraph V E)
    (u v : V) (hu : u ≠ v) (e : E)
    (T : {T : J.SpanningTree // e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v}) :
    J.signedPathTraversal T.val u v e =
      (if J.reaches (treeCutEquiv J u v hu e T).val.val (J.left e) u then (1 : ℝ) else 0) -
      (if J.reaches (treeCutEquiv J u v hu e T).val.val (J.right e) u then (1 : ℝ) else 0) := by
  let F := treeCutEquiv J u v hu e T
  have hcolors : ¬(J.reaches F.val.val (J.left e) u ↔
      J.reaches F.val.val (J.right e) u) := fun h =>
    F.property ((twoRootForest_reaches_iff J u v F.val (J.left e) (J.right e)).mpr h)
  have hleft : J.reaches (T.val.val.erase e) u (J.left e) ↔
      J.reaches F.val.val (J.left e) u :=
    ⟨fun h => reaches_symm J h, fun h => reaches_symm J h⟩
  change J.signedPathTraversal T.val u v e =
    (if J.reaches F.val.val (J.left e) u then (1 : ℝ) else 0) -
    (if J.reaches F.val.val (J.right e) u then (1 : ℝ) else 0)
  rw [signedPathTraversal, if_pos T.property]
  by_cases hl : J.reaches F.val.val (J.left e) u
  · have hr : ¬J.reaches F.val.val (J.right e) u := fun hr =>
      hcolors ⟨fun _ => hr, fun _ => hl⟩
    simp [hl, hr, hleft.mpr hl]
  · have hr : J.reaches F.val.val (J.right e) u := by
      by_contra hr
      exact hcolors ⟨fun h => (hl h).elim, fun h => (hr h).elim⟩
    have hn : ¬J.reaches (T.val.val.erase e) u (J.left e) := fun h => hl (hleft.mp h)
    simp [hl, hr, hn]

variable [Fintype E]

/-- The literal forest count is the finite sum of first-root component indicators. -/
theorem forestColorCount_eq_sum (J : CopiedGraph V E) (u v x : V) :
    (forestColorCount J u v x : ℝ) =
      ∑ F : J.TwoRootForest u v, if J.reaches F.val x u then (1 : ℝ) else 0 := by
  rw [forestColorCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.natCast_card_filter _ _

/-- The sum of signed tree traversals is exactly the difference of literal
first-root forest counts at the stored endpoints. All original copies are kept;
no graph connectivity or determinant formula is required. -/
theorem sum_signedPathTraversal_eq_count_sub (J : CopiedGraph V E)
    (u v : V) (hu : u ≠ v) (e : E) :
    (∑ T : J.SpanningTree, J.signedPathTraversal T u v e) =
      (forestColorCount J u v (J.left e) : ℝ) -
        (forestColorCount J u v (J.right e) : ℝ) := by
  let treeEvent : Set J.SpanningTree :=
    {T | e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v}
  let forestEvent : Set (J.TwoRootForest u v) :=
    {F | ¬J.reaches F.val (J.left e) (J.right e)}
  let weight (F : J.TwoRootForest u v) : ℝ :=
    (if J.reaches F.val (J.left e) u then 1 else 0) -
    (if J.reaches F.val (J.right e) u then 1 else 0)
  calc
    _ = ∑ T : treeEvent, J.signedPathTraversal T.val u v e := by
      apply Finset.sum_congr_set treeEvent _ _
      · intro T _
        rfl
      · intro T hT
        exact if_neg hT
    _ = ∑ F : forestEvent, weight F.val := by
      apply Fintype.sum_equiv (treeCutEquiv J u v hu e)
      intro T
      exact signedPathTraversal_treeCutEquiv J u v hu e T
    _ = ∑ F : J.TwoRootForest u v, weight F := by
      symm
      apply Finset.sum_congr_set forestEvent _ _
      · intro F _
        rfl
      · intro F hF
        have hreach : J.reaches F.val (J.left e) (J.right e) := not_not.mp hF
        have hcolors := (twoRootForest_reaches_iff J u v F (J.left e) (J.right e)).mp hreach
        simp only [weight, hcolors, sub_self]
    _ = _ := by
      simp only [weight, Finset.sum_sub_distrib, ← forestColorCount_eq_sum]

end
end LatticeProb.Graph.CopiedGraph
