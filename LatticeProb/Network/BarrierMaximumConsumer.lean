import LatticeProb.Network.BarrierMaximum

/-!
# A coercive barrier on the infinite ray

The nearest-neighbor graph on the natural numbers has barrier `v(n) = n`, harmonic away
from its pole at zero. The barrier maximum principle implies that every bounded-above
function harmonic at the positive integers is bounded by its value at zero.
-/

namespace LatticeProb.Network.Ray

open LatticeProb.Graph

/-- The infinite ray, using the Hasse graph of the usual order on natural numbers. -/
def graph : SimpleGraph ℕ := SimpleGraph.hasse ℕ

/-- Two vertices of the ray are adjacent exactly when they differ by one. -/
theorem graph_adj (m n : ℕ) : graph.Adj m n ↔ m + 1 = n ∨ n + 1 = m := by
  simp only [graph, SimpleGraph.hasse_adj, Nat.covBy_iff_add_one_eq]

/-- Every neighbor of `n` lies in the finite interval from zero to `n + 1`. -/
noncomputable instance : graph.LocallyFinite := fun n =>
  ((Set.finite_le_nat (n + 1)).subset (by
    intro m hm
    have h := (graph_adj n m).mp hm
    change m ≤ n + 1
    omega)).fintype

/-- The infinite ray is connected. -/
theorem graph_connected : graph.Connected :=
  ⟨SimpleGraph.hasse_preconnected_of_succ ℕ⟩

/-- A positive vertex has exactly its predecessor and successor as neighbors. -/
theorem neighborFinset_succ (n : ℕ) : graph.neighborFinset (n + 1) = {n, n + 2} := by
  ext m
  simp only [SimpleGraph.mem_neighborFinset, graph_adj, Finset.mem_insert,
    Finset.mem_singleton]
  omega

/-- The linear barrier is harmonic away from the pole at zero. -/
theorem harmonic_cast : HarmonicOn graph (unitCond graph) (fun n => (n : ℝ)) {n | n ≠ 0} := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [netLaplacian_unitCond]
  unfold LatticeProb.Graph.laplacian
  rw [neighborFinset_succ, Finset.sum_pair (by omega : k ≠ k + 2)]
  push_cast
  ring

/-- Every real sublevel set of the linear barrier on the positive ray is finite. -/
theorem finite_sublevel (r : ℝ) : {n : ℕ | n ≠ 0 ∧ (n : ℝ) ≤ r}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt r
  refine (Set.finite_le_nat N).subset ?_
  intro n hn
  have hcast : (n : ℝ) ≤ N := hn.2.trans hN.le
  exact_mod_cast hcast

/-- A bounded-above harmonic function on the positive ray is bounded by its value at zero.
All graph, boundary and barrier hypotheses are discharged for this concrete infinite domain. -/
theorem le_at_zero (f : ℕ → ℝ) (B : ℝ)
    (hf : HarmonicOn graph (unitCond graph) f {n | n ≠ 0})
    (hbounded : ∀ n, n ≠ 0 → f n ≤ B) : ∀ n, f n ≤ f 0 := by
  have hbound := le_of_coercive_barrier graph_connected isCond_unitCond {n : ℕ | n ≠ 0}
    ⟨0, fun h => h rfl⟩ f (fun n => (n : ℝ)) (f 0) B hf harmonic_cast hbounded
    (fun n => Nat.cast_nonneg n) finite_sublevel (by
      intro n hn
      have hn0 : n = 0 := Classical.not_not.mp hn.1
      rw [hn0])
  intro n
  by_cases hn : n = 0
  · rw [hn]
  · exact hbound n hn

/-- Applying the barrier argument to both signs gives uniqueness of bounded harmonic data
on the ray with a single boundary vertex. -/
theorem eq_at_zero (f : ℕ → ℝ) (B : ℝ)
    (hf : HarmonicOn graph (unitCond graph) f {n | n ≠ 0})
    (hbounded : ∀ n, |f n| ≤ B) : ∀ n, f n = f 0 := by
  have hu := le_at_zero f B hf (fun n _ => (le_abs_self (f n)).trans (hbounded n))
  have hneg : HarmonicOn graph (unitCond graph) (fun n => -f n) {n | n ≠ 0} := by
    intro n hn
    rw [netLaplacian_neg, hf n hn, neg_zero]
  have hl := le_at_zero (fun n => -f n) B hneg
    (fun n _ => (neg_le_abs (f n)).trans (hbounded n))
  intro n
  exact le_antisymm (hu n) (neg_le_neg_iff.mp (hl n))

end LatticeProb.Network.Ray
