import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exponential decay beats the `4ⁿ` count of dyadic cells

If `p n ≤ exp (-(c n))` for all large `n`, with `c > log 4`, and each `p n` is finite, then
`∑ₙ 4ⁿ p n < ∞`.  (Finiteness of every `p n` is needed: a single infinite term makes the sum
infinite.)

* `LatticeProb.LQG.tsum_four_pow_mul_ne_top_of_eventually_le_exp`: the finiteness.
-/

open scoped ENNReal

namespace LatticeProb.LQG

/-- `4ⁿ · exp (-(c n)) = exp (log 4 - c) ^ n`, as extended nonnegative reals. -/
private theorem four_pow_mul_ofReal_exp_neg (c : ℝ) (n : ℕ) :
    (4 : ℝ≥0∞) ^ n * ENNReal.ofReal (Real.exp (-(c * n))) =
      ENNReal.ofReal (Real.exp (Real.log 4 - c) ^ n) := by
  have h4 : (4 : ℝ≥0∞) ^ n = ENNReal.ofReal ((4 : ℝ) ^ n) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [h4, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_nat_mul]
  congr 1
  rw [← Real.exp_log (show (0 : ℝ) < 4 by norm_num), ← Real.exp_nat_mul, ← Real.exp_add]
  rw [Real.exp_log (show (0 : ℝ) < 4 by norm_num)]
  congr 1
  ring

/-- **Exponential tails beat the `4ⁿ` dyadic cell count.** If every `p n` is finite and
`p n ≤ exp (-(c n))` for all large `n`, where `c > log 4`, then `∑ₙ 4ⁿ p n ≠ ∞`. -/
theorem tsum_four_pow_mul_ne_top_of_eventually_le_exp {p : ℕ → ℝ≥0∞} {c : ℝ}
    (hc : Real.log 4 < c) (hfin : ∀ n, p n ≠ ⊤)
    (hp : ∀ᶠ n in Filter.atTop, p n ≤ ENNReal.ofReal (Real.exp (-(c * n)))) :
    ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p n ≠ ⊤ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hp
  set r : ℝ := Real.exp (Real.log 4 - c) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  set a : ℕ → ℝ≥0∞ := fun n => if n < N then (4 : ℝ≥0∞) ^ n * p n else 0 with ha
  have hbound : ∀ n, (4 : ℝ≥0∞) ^ n * p n ≤ a n + ENNReal.ofReal (r ^ n) := by
    intro n
    by_cases hn : n < N
    · have : a n = (4 : ℝ≥0∞) ^ n * p n := by simp [ha, hn]
      rw [this]
      exact le_self_add
    · have hn' : N ≤ n := not_lt.1 hn
      have : a n = 0 := by simp [ha, hn]
      rw [this, zero_add]
      calc (4 : ℝ≥0∞) ^ n * p n
          ≤ (4 : ℝ≥0∞) ^ n * ENNReal.ofReal (Real.exp (-(c * n))) :=
            mul_le_mul_right (hN n hn') _
        _ = ENNReal.ofReal (r ^ n) := four_pow_mul_ofReal_exp_neg c n
  have ha_fin : ∑' n, a n ≠ ⊤ := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · refine ENNReal.sum_ne_top.2 fun n hn => ?_
      have hn' : n < N := Finset.mem_range.1 hn
      have : a n = (4 : ℝ≥0∞) ^ n * p n := by simp [ha, hn']
      rw [this]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (hfin n)
    · intro n hn
      have : ¬ n < N := fun h => hn (Finset.mem_range.2 h)
      simp [ha, this]
  have hgeom : ∑' n : ℕ, ENNReal.ofReal (r ^ n) ≠ ⊤ := by
    have hs : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg hr0 n) hs]
    exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_add]
  exact ENNReal.add_ne_top.2 ⟨ha_fin, hgeom⟩

end LatticeProb.LQG
