/- Conservation of signed current on each copied tree path.
All copies retain their original identities; loops and equal terminals are included. -/
import LatticeProb.Graph.CopiedGraph.IncidentPath
import LatticeProb.Graph.CopiedGraph.SignedPathTraversal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*}

/-- Signed traversal is additive in its terminals, including coincident terminals. -/
theorem signedPathTraversal_add (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v w : V) (e : E) :
    J.signedPathTraversal T u w e =
      J.signedPathTraversal T u v e + J.signedPathTraversal T v w e := by
  rw [signedPathTraversal_eq_cut_difference, signedPathTraversal_eq_cut_difference,
    signedPathTraversal_eq_cut_difference]
  by_cases he : e ∈ T.val
  · simp only [if_pos he]
    ring
  · simp [he]


/-- An incident copy on the path leaving its first vertex contributes one unit. -/
theorem signedPathTraversal_root_incidence (J : CopiedGraph V E)
    (T : J.SpanningTree) (x q : V) (e : E) :
    ((if J.left e = x then J.signedPathTraversal T x q e else 0) -
      (if J.right e = x then J.signedPathTraversal T x q e else 0)) =
    if e ∈ T.val ∧ (J.left e = x ∨ J.right e = x) ∧
      ¬J.reaches (T.val.erase e) x q then (1 : ℝ) else 0 := by
  by_cases he : e ∈ T.val
  · have hne : J.left e ≠ J.right e := by
      intro h
      exact J.loop_not_mem T e h he
    by_cases hl : J.left e = x
    · have hr : J.right e ≠ x := fun h => hne (hl.trans h.symm)
      have hxx : J.reaches (T.val.erase e) x x := .refl
      simp [signedPathTraversal, he, hl, hr, hxx]
    · by_cases hr : J.right e = x
      · have hn : ¬J.reaches (T.val.erase e) x (J.left e) := by
          intro h
          apply T.property.2.2 e he
          rw [hr]
          exact J.reaches_symm h
        by_cases hcut : J.reaches (T.val.erase e) x q <;>
          simp [signedPathTraversal, he, hl, hr, hn, hcut]
      · simp [hl, hr]
  · simp [signedPathTraversal, he]

/-- Exactly one incident copy leaves a vertex toward a distinct vertex of a tree. -/
theorem existsUnique_incident_path_copy (J : CopiedGraph V E) (T : J.SpanningTree)
    (x q : V) (hxq : x ≠ q) :
    ∃! e, e ∈ T.val ∧ (J.left e = x ∨ J.right e = x) ∧
      ¬J.reaches (T.val.erase e) x q := by
  obtain ⟨e, he, hi, hc⟩ := J.forest_path_incident_exists T.val T.property.2.2
    x q hxq (T.property.2.1 x q)
  refine ⟨e, ⟨he, hi, hc⟩, ?_⟩
  intro f hf
  exact J.tree_path_incident_unique T x q f e hf.1 hf.2.1 hi hf.2.2 hc

variable [Fintype E]

/-- The path from a vertex to a distinct terminal has divergence one there. -/
theorem signedPathTraversal_root_divergence (J : CopiedGraph V E)
    (T : J.SpanningTree) (x q : V) :
    (∑ e : E,
      ((if J.left e = x then J.signedPathTraversal T x q e else 0) -
        (if J.right e = x then J.signedPathTraversal T x q e else 0))) =
    if x = q then (0 : ℝ) else 1 := by
  by_cases hxq : x = q
  · subst q
    simp [signedPathTraversal_self]
  · obtain ⟨e, he, hunique⟩ := J.existsUnique_incident_path_copy T x q hxq
    rw [if_neg hxq]
    calc
      _ = ∑ f : E, if f = e then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro f _
        rw [signedPathTraversal_root_incidence]
        by_cases hfe : f = e
        · subst f
          simp [he]
        · have hn : ¬(f ∈ T.val ∧ (J.left f = x ∨ J.right f = x) ∧
              ¬J.reaches (T.val.erase f) x q) := fun h => hfe (hunique f h)
          simp [hfe, hn]
      _ = 1 := by simp

/-- Signed traversal is conserved at every vertex except its two terminals. -/
theorem signedPathTraversal_divergence (J : CopiedGraph V E) (T : J.SpanningTree)
    (u v x : V) :
    (∑ e : E,
      ((if J.left e = x then J.signedPathTraversal T u v e else 0) -
        (if J.right e = x then J.signedPathTraversal T u v e else 0))) =
    (if x = u then (1 : ℝ) else 0) - (if x = v then (1 : ℝ) else 0) := by
  have hpath (e : E) : J.signedPathTraversal T u v e =
      J.signedPathTraversal T x v e - J.signedPathTraversal T x u e := by
    have h := J.signedPathTraversal_add T x u v e
    linarith
  calc
    _ = (∑ e : E,
          ((if J.left e = x then J.signedPathTraversal T x v e else 0) -
            (if J.right e = x then J.signedPathTraversal T x v e else 0))) -
        (∑ e : E,
          ((if J.left e = x then J.signedPathTraversal T x u e else 0) -
            (if J.right e = x then J.signedPathTraversal T x u e else 0))) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rw [hpath]
      split_ifs <;> ring
    _ = _ := by
      rw [signedPathTraversal_root_divergence, signedPathTraversal_root_divergence]
      split_ifs <;> norm_num


end
end LatticeProb.Graph.CopiedGraph
