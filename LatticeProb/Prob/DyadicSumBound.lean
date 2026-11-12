import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite total of dyadic double sums from a uniform bound at each level

If the quantities `q n i j`, `i, j < 2ⁿ`, are bounded at level `n` by `p n` and
`∑ₙ 4ⁿ p n < ∞`, then the total `∑ₙ ∑_{i,j<2ⁿ} q n i j` is finite.

* `LatticeProb.LQG.tsum_tsum_sum_le_of_le_four_pow`: the finiteness.
-/

open scoped ENNReal

namespace LatticeProb.LQG

/-- **Uniform bounds on the `4ⁿ` dyadic cells give a finite total.** If `q n i j ≤ p n` for all
`i, j < 2ⁿ` and `∑ₙ 4ⁿ p n ≠ ∞`, then `∑ₙ ∑_{i<2ⁿ} ∑_{j<2ⁿ} q n i j ≠ ∞`. -/
theorem tsum_tsum_sum_le_of_le_four_pow {q : ℕ → ℕ → ℕ → ℝ≥0∞} {p : ℕ → ℝ≥0∞}
    (hq : ∀ n i j, i < 2 ^ n → j < 2 ^ n → q n i j ≤ p n) (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∑' n, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), q n i j ≠ ⊤ := by
  refine ne_top_of_le_ne_top hp (ENNReal.tsum_le_tsum fun n => ?_)
  calc ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n), q n i j
      ≤ ∑ _i ∈ Finset.range (2 ^ n), ∑ _j ∈ Finset.range (2 ^ n), p n :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
          hq n i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)
    _ = 4 ^ n * p n := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_assoc, ← Nat.cast_mul, ← pow_two, ← pow_mul, mul_comm n 2, pow_mul]
        norm_num

end LatticeProb.LQG
