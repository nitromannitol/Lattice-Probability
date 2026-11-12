import Mathlib

/-!
# Summability of exponentially weighted sequences with an eventual exponential bound

Let `M : ℕ → ℝ≥0∞` be a sequence of finite values with `M k ≤ e^{-(c + η) k}` for all large `k`, where `η > 0`.
Then the weighted series `∑ₖ e^{c k} M k` is finite: its terms are eventually bounded by the geometric sequence
`e^{-η k}`, and the finitely many remaining terms are finite.

This is the deterministic summation step in shell (multiscale) chaining arguments: when the size `M k` of the `k`-th
exponential shell `{e^{-(k+1)} ≤ |x| ≤ e^{-k}}` decays faster than the weight `e^{c k}` grows, the chained bound is
finite.
-/

open Filter Finset
open scoped ENNReal

namespace LatticeProb

/-- **Eventual exponential decay beats an exponential weight.** If `M k` is finite for every `k` and
`M k ≤ e^{-(c + η) k}` for all large `k`, with `η > 0`, then `∑ₖ e^{c k} M k < ∞`. -/
theorem tsum_ofReal_exp_mul_mul_ne_top_of_eventually_le {M : ℕ → ℝ≥0∞} {c η : ℝ} (hη : 0 < η)
    (hfin : ∀ k, M k ≠ ⊤)
    (hM : ∀ᶠ k in atTop, M k ≤ ENNReal.ofReal (Real.exp (-(c + η) * k))) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (c * k)) * M k ≠ ⊤ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hM
  set f : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (c * k)) * M k with hf_def
  have hf : ∀ k, f k ≠ ⊤ := fun k => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin k)
  -- the geometric ratio `e^{-η} < 1`
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-η)) with hr_def
  have hr : r < 1 := ENNReal.ofReal_lt_one.2 (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith))
  -- each tail term is at most `r ^ k`
  have htail : ∀ k : ℕ, f (k + N) ≤ r ^ k := by
    intro k
    calc f (k + N)
        ≤ ENNReal.ofReal (Real.exp (c * ((k + N : ℕ) : ℝ))) *
            ENNReal.ofReal (Real.exp (-(c + η) * ((k + N : ℕ) : ℝ))) :=
          mul_le_mul' le_rfl (hN _ (Nat.le_add_left N k))
      _ = ENNReal.ofReal (Real.exp (-η) ^ (k + N)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_nat_mul]
          congr 2
          ring
      _ ≤ ENNReal.ofReal (Real.exp (-η) ^ k) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [pow_add]
          refine mul_le_of_le_one_right (pow_nonneg (Real.exp_pos _).le _) ?_
          exact pow_le_one₀ (Real.exp_pos _).le
            (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith))
      _ = r ^ k := by rw [hr_def, ENNReal.ofReal_pow (Real.exp_pos _).le]
  have hsplit := (ENNReal.summable : Summable fun k => f (k + N)).sum_add_tsum_nat_add'
  change ∑' k : ℕ, f k ≠ ⊤
  rw [← hsplit]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun k _ => hf k, ?_⟩
  exact ne_top_of_le_ne_top (tsum_geometric_lt_top.2 hr).ne (ENNReal.tsum_le_tsum htail)

end LatticeProb
