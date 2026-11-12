/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7PercChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7PercIndep
import Mathlib.Data.List.Chain

/-!
# DZZ Lemma 3.7: a connected set is traversed by one chain (P2-DZZ3E)

Encoding step for DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 1001–1010 ("a sequence of
neighbouring boxes enclosing `B`"): a set `U` in which any two points are joined by an
`r`-path is traversed by a single `r`-chain visiting any prescribed finite list of its points
(own elementary argument: concatenate paths, `List.exists_isChain_cons_of_relationReflTransGen`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric
namespace DZZ

/-- One `r`-chain from `start` visiting all points of `L`, when all points are `r`-connected. -/
theorem exists_isChain_cover {α : Type*} {r : α → α → Prop} {U : Set α}
    (hconn : ∀ x ∈ U, ∀ y ∈ U, Relation.ReflTransGen r x y) :
    ∀ (L : List α), (∀ x ∈ L, x ∈ U) → ∀ start ∈ U,
      ∃ l, List.IsChain r (start :: l) ∧ ∀ x ∈ L, x ∈ start :: l := by
  intro L
  induction L with
  | nil => intro _ start _; exact ⟨[], .singleton _, by simp⟩
  | cons a L' ih =>
    intro hL start hs
    have ha : a ∈ U := hL a List.mem_cons_self
    obtain ⟨l', hc', hcov'⟩ := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) a ha
    obtain ⟨l1, hc1, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen (hconn _ hs _ ha)
    have hsplit := List.dropLast_append_getLast (List.cons_ne_nil start l1)
    rw [hlast] at hsplit
    have e : start :: (l1 ++ l') = (start :: l1).dropLast ++ a :: l' := by
      conv_lhs => rw [← List.cons_append, ← hsplit]
      rw [List.append_assoc, List.singleton_append]
    refine ⟨l1 ++ l', ?_, ?_⟩
    · rw [e, List.isChain_split, hsplit]; exact ⟨hc1, hc'⟩
    · have haM : a ∈ start :: (l1 ++ l') := by
        rw [e]; exact List.mem_append_right _ List.mem_cons_self
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact haM
      · rcases List.mem_cons.1 (hcov' x hx) with rfl | hx'
        · exact haM
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ hx')

end DZZ
end LQGMetric
