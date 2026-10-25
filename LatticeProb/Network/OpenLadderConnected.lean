import LatticeProb.Network.OpenLadder
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectedness of the open ladder

Every left rung is reached by climbing the left column from the source.
A horizontal rung edge reaches the right column, and the bottom right edge reaches the target.
-/

namespace LatticeProb.Network.OpenLadder

/-- Climbing the actual left-column edges reaches every positive natural rung. -/
theorem source_reachable_left_nat {n : ℤ} (k : ℕ) (hk : (k : ℤ) + 1 ≤ n) :
    (graph n).Reachable (source n) (left n ((k : ℤ) + 1) ⟨by omega, hk⟩) := by
  induction k with
  | zero =>
    apply SimpleGraph.Adj.reachable
    change (1 = 2 ∧ _) ∨ (1 = 0 + 1 ∧ (1 + 1 = 2 ∨ 2 + 1 = 1))
    omega
  | succ k ih =>
    have hp := ih (by omega)
    refine hp.trans (SimpleGraph.Adj.reachable ?_)
    change (2 = 2 ∧ ((k : ℤ) + 1 + 1 = (↑(k + 1) : ℤ) + 1 ∨ _)) ∨ _
    omega

/-- Every actual left rung is reachable from the source along the left column. -/
theorem source_reachable_left {n j : ℤ} (hj : 1 ≤ j ∧ j ≤ n) :
    (graph n).Reachable (source n) (left n j hj) := by
  have he : (((j - 1).toNat : ℕ) : ℤ) + 1 = j := by omega
  have h := source_reachable_left_nat (j - 1).toNat (n := n) (by omega)
  simpa only [he] using h

/-- The horizontal edge on each actual rung reaches its right vertex. -/
theorem source_reachable_right {n j : ℤ} (hj : 1 ≤ j ∧ j ≤ n) :
    (graph n).Reachable (source n) (right n j hj) := by
  refine (source_reachable_left hj).trans (SimpleGraph.Adj.reachable ?_)
  change (2 = 3 ∧ _) ∨ (j = j ∧ (2 + 1 = 3 ∨ 3 + 1 = 2))
  omega

/-- The right bottom rung and its leaf edge give a path to the target. -/
theorem source_reachable_target {n : ℤ} (hn : 1 ≤ n) :
    (graph n).Reachable (source n) (target n) := by
  refine (source_reachable_right ⟨by omega, hn⟩).trans (SimpleGraph.Adj.reachable ?_)
  change (3 = 4 ∧ _) ∨ (1 = 1 ∧ (3 + 1 = 4 ∨ 4 + 1 = 3))
  omega

/-- The actual finite open ladder is connected at every positive integer height. -/
theorem connected {n : ℤ} (hn : 1 ≤ n) : (graph n).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨source n, fun v => ?_⟩
  by_cases hs : v = source n
  · subst v
    exact SimpleGraph.Reachable.rfl
  by_cases ht : v = target n
  · subst v
    exact source_reachable_target hn
  obtain ⟨j, hj, hv⟩ := eq_left_or_right hn v hs ht
  rcases hv with rfl | rfl
  · exact source_reachable_left hj
  · exact source_reachable_right hj

/-- At height two the explicit column and rung paths connect all six actual vertices. -/
theorem connected_two : (graph 2).Connected := connected (by omega)

end LatticeProb.Network.OpenLadder
