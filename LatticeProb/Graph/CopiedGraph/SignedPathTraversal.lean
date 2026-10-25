module

/-
Signed traversal on original copied tree paths. The definition and its zero-case
proofs are adapted from finite-avalanches, Electrical/Trees/SignedPathTraversal.
The cut-color identity uses only the exact elementary rooted forest predicate.
-/
public import LatticeProb.Graph.CopiedGraph.TwoRootForest
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type*}

/-- Signed traversal of an original copy on the source-to-target tree path,
positive in the stored left-to-right direction. -/
def signedPathTraversal (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v : V) (e : E) : ℝ :=
  if e ∈ T.val ∧ ¬J.reaches (T.val.erase e) u v then
    if J.reaches (T.val.erase e) u (J.left e) then 1 else -1
  else 0

/-- A path with equal terminals traverses no copy. -/
theorem signedPathTraversal_self (J : CopiedGraph V E) (T : J.SpanningTree)
    (u : V) (e : E) : J.signedPathTraversal T u u e = 0 := by
  simp only [signedPathTraversal, not_true_eq_false, and_false, ↓reduceIte,
    show J.reaches (T.val.erase e) u u from .refl]

/-- An original loop has zero signed traversal. -/
theorem signedPathTraversal_loop (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v : V) (e : E) (he : J.left e = J.right e) :
    J.signedPathTraversal T u v e = 0 := by
  simp [signedPathTraversal, J.loop_not_mem T e he]

/-- The source component determines the positive orientation, without choosing a path. -/
theorem signedPathTraversal_eq_of_separates (J : CopiedGraph V E)
    (T : J.SpanningTree) (u v : V) (e : E) (he : e ∈ T.val)
    (hsep : ¬J.reaches (T.val.erase e) u v)
    (hl : J.reaches (T.val.erase e) u (J.left e)) :
    J.signedPathTraversal T u v e = 1 := by
  simp [signedPathTraversal, he, hsep, hl]

/-- Signed traversal is the difference of terminal colors in the component
of the stored left endpoint after deletion of the selected original copy.
This includes equal terminals, absent copies, and loops. -/
theorem signedPathTraversal_eq_cut_difference (J : CopiedGraph V E)
    (T : J.SpanningTree) (u v : V) (e : E) :
    J.signedPathTraversal T u v e =
      if e ∈ T.val then
        (if J.reaches (T.val.erase e) u (J.left e) then (1 : ℝ) else 0) -
        (if J.reaches (T.val.erase e) v (J.left e) then (1 : ℝ) else 0)
      else 0 := by
  by_cases he : e ∈ T.val
  · let F : J.TwoRootForest (J.left e) (J.right e) :=
      ⟨T.val.erase e, tree_erase_twoRootForest J T e he⟩
    have huv : J.reaches (T.val.erase e) u v ↔
        (J.reaches (T.val.erase e) u (J.left e) ↔
          J.reaches (T.val.erase e) v (J.left e)) :=
      twoRootForest_reaches_iff J (J.left e) (J.right e) F u v
    by_cases hu : J.reaches (T.val.erase e) u (J.left e) <;>
      by_cases hv : J.reaches (T.val.erase e) v (J.left e) <;>
        simp [signedPathTraversal, he, huv, hu, hv]
  · simp [signedPathTraversal, he]

end
end LatticeProb.Graph.CopiedGraph
