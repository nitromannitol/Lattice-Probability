/-
Ottaviani's maximal inequality, in the form of a first passage decomposition.

A maximal bound for a process is bought from a bound at the last time alone:
if the process first reaches the level `2 α` at index `k`, and if the remaining
increment from `k` to the end is smaller than `α`, then the value at the end is
at least `α`.  The first passage sets are disjoint, so summing the probabilities
of these two events, which are independent because the first depends on the past
and the second on the future, bounds the probability of ever reaching `2 α` by
the probability of ending above `α`, divided by the probability that no
remaining increment is large.

Nothing here is about a particular process: the independence, the disjointness
and the inclusion enter as hypotheses, and the conclusion is the inequality
between the two probabilities.  The application to Brownian motion is in
`LatticeProb/Prob/BrownianMax.lean`.
-/
import Mathlib

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- **Ottaviani's maximal inequality**, as a first passage decomposition.  `A k` is the
event that the first passage above the level happens at index `k`, `G k` the event that
the increment from `k` to the end is small, `E` the event that the end value is large and
`M` the event that the level is ever reached.  If the `A k` are disjoint, if each `A k` is
independent of `G k`, if each `G k` has probability at least `r`, and if `A k ∩ G k ⊆ E`,
then `r * P M ≤ P E`. -/
theorem ottaviani {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {A G : ℕ → Set Ω} {E M : Set Ω} {r : ℝ≥0∞}
    (hAm : ∀ k, MeasurableSet (A k)) (hGm : ∀ k, MeasurableSet (G k))
    (hdisj : ∀ j k, j ≠ k → Disjoint (A j) (A k))
    (hindep : ∀ k ≤ N, P (A k ∩ G k) = P (A k) * P (G k))
    (hG : ∀ k ≤ N, r ≤ P (G k))
    (hsub : ∀ k ≤ N, A k ∩ G k ⊆ E)
    (hM : M ⊆ ⋃ k ∈ Finset.range (N + 1), A k) :
    r * P M ≤ P E := by
  classical
  have hpd : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint A := fun i _ j _ hij =>
    hdisj i j hij
  have hpd2 : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint (fun k => A k ∩ G k) :=
    fun i _ j _ hij =>
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left (hdisj i j hij)
  have h1 : P (⋃ k ∈ Finset.range (N + 1), A k) = ∑ k ∈ Finset.range (N + 1), P (A k) :=
    measure_biUnion_finset hpd (fun k _ => hAm k)
  have h2 : P (⋃ k ∈ Finset.range (N + 1), (A k ∩ G k))
      = ∑ k ∈ Finset.range (N + 1), P (A k ∩ G k) :=
    measure_biUnion_finset hpd2 (fun k _ => (hAm k).inter (hGm k))
  have h3 : ∀ k ∈ Finset.range (N + 1), r * P (A k) ≤ P (A k ∩ G k) := by
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hindep k hkN, mul_comm (P (A k)) (P (G k))]
    exact mul_le_mul_left (hG k hkN) (P (A k))
  have h4 : (⋃ k ∈ Finset.range (N + 1), (A k ∩ G k)) ⊆ E :=
    Set.iUnion₂_subset fun k hk => hsub k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  calc r * P M
      ≤ r * P (⋃ k ∈ Finset.range (N + 1), A k) := mul_le_mul_right (measure_mono hM) r
    _ = ∑ k ∈ Finset.range (N + 1), r * P (A k) := by rw [h1, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (N + 1), P (A k ∩ G k) := Finset.sum_le_sum h3
    _ = P (⋃ k ∈ Finset.range (N + 1), (A k ∩ G k)) := h2.symm
    _ ≤ P E := measure_mono h4

end LatticeProb

end
