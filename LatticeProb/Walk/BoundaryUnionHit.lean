import LatticeProb.Graph.Boundary
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime

/-!
# Hitting the inner boundary before exit

A graph path started inside a set reaches its inner boundary before it can
leave, even if the path is allowed to stay at its current vertex.
-/

set_option autoImplicit false

open Set MatedCRTHarmonic.Markov

namespace LatticeProb

variable {V : Type*} (G : SimpleGraph V) (A : Set V) (x : ℕ → V)

/-- Every visit to the complement is preceded by a visit to the inner boundary. -/
theorem exists_innerBoundary_before_compl (hstart : x 0 ∈ A)
    (hstep : ∀ n, x (n + 1) = x n ∨ G.Adj (x n) (x (n + 1))) :
    ∀ n, x n ∉ A → ∃ j < n, x j ∈ Graph.innerBoundary G A := by
  intro n
  induction n with
  | zero =>
    intro hn
    exact (hn hstart).elim
  | succ n ih =>
    intro hn
    by_cases h : x n ∈ A
    · refine ⟨n, Nat.lt_succ_self n, h, x (n + 1), hn, ?_⟩
      rcases hstep n with heq | hadj
      · exact (hn (heq ▸ h)).elim
      · exact hadj
    · obtain ⟨j, hj, hmem⟩ := ih h
      exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self n), hmem⟩

/-- Adding the complement to the target does not change the first boundary hit. -/
theorem hitTime_compl_union_innerBoundary (hstart : x 0 ∈ A)
    (hstep : ∀ n, x (n + 1) = x n ∨ G.Adj (x n) (x (n + 1))) :
    hitTime (Aᶜ ∪ Graph.innerBoundary G A) x =
      hitTime (Graph.innerBoundary G A) x := by
  apply le_antisymm
  · apply le_hitTime_iff.mpr
    intro n hn
    exact hitTime_le_of_mem (Or.inr hn)
  · apply le_hitTime_iff.mpr
    intro n hn
    rcases hn with hn | hn
    · obtain ⟨j, hj, hmem⟩ := exists_innerBoundary_before_compl G A x hstart hstep n hn
      exact le_trans (hitTime_le_of_mem hmem) (by exact_mod_cast hj.le)
    · exact hitTime_le_of_mem hn

end LatticeProb
