import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Shifting the `4ⁿ`-weighted tail series by a growing index

If `∑ₙ 4ⁿ p n < ∞`, then shifting the index by `m` gives
`∑ₙ 4ⁿ p (n + m) ≤ 4⁻ᵐ ∑ₙ 4ⁿ p n`, so the double series over a shift `m k` of the level, with
`∑ₖ 4⁻ᵐ⁽ᵏ⁾ < ∞`, is finite; this holds for `m k = ⌈κ k⌉₊` with `κ > 0`.

* `LatticeProb.tsum_four_pow_mul_shift_le`: the bound for one shift.
* `LatticeProb.tsum_tsum_four_pow_mul_shift_ne_top`: the double series.
* `LatticeProb.tsum_inv_four_pow_ceil_ne_top`: `∑ₖ 4^{-⌈κ k⌉} < ∞` for `κ > 0`.
* `LatticeProb.tsum_tsum_four_pow_mul_ceil_shift_ne_top`: the double series for `m k = ⌈κ k⌉₊`.
-/

open scoped ENNReal

namespace LatticeProb

/-- **Shift bound.** `∑ₙ 4ⁿ p (n + m) ≤ 4⁻ᵐ ∑ₙ 4ⁿ p n`. -/
theorem tsum_four_pow_mul_shift_le (p : ℕ → ℝ≥0∞) (m : ℕ) :
    ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p (n + m) ≤
      ((4 : ℝ≥0∞) ^ m)⁻¹ * ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p n := by
  have h0 : (4 : ℝ≥0∞) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have htop : (4 : ℝ≥0∞) ^ m ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have h1 : (4 : ℝ≥0∞) ^ m * ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p (n + m) ≤
      ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p n := by
    rw [← ENNReal.tsum_mul_left]
    have : ∀ n : ℕ, (4 : ℝ≥0∞) ^ m * ((4 : ℝ≥0∞) ^ n * p (n + m)) =
        (fun j : ℕ => (4 : ℝ≥0∞) ^ j * p j) (n + m) := by
      intro n
      simp only [pow_add]
      ring
    simp_rw [this]
    exact ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective m)
      (fun j : ℕ => (4 : ℝ≥0∞) ^ j * p j)
  calc ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p (n + m)
      = ((4 : ℝ≥0∞) ^ m)⁻¹ * ((4 : ℝ≥0∞) ^ m * ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p (n + m)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
    _ ≤ ((4 : ℝ≥0∞) ^ m)⁻¹ * ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p n := by gcongr

/-- **Double series over a shift of the level.** If `∑ₙ 4ⁿ p n < ∞` and `∑ₖ 4⁻ᵐ⁽ᵏ⁾ < ∞`, then
`∑ₖ ∑ₙ 4ⁿ p (n + m k) < ∞`. -/
theorem tsum_tsum_four_pow_mul_shift_ne_top {p : ℕ → ℝ≥0∞} {m : ℕ → ℕ}
    (hp : ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p n ≠ ⊤)
    (hm : ∑' k : ℕ, ((4 : ℝ≥0∞) ^ m k)⁻¹ ≠ ⊤) :
    ∑' k : ℕ, ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p (n + m k) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k => tsum_four_pow_mul_shift_le p (m k))
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top hm hp

/-- For `κ > 0`, `∑ₖ 4^{-⌈κ k⌉} < ∞`. -/
theorem tsum_inv_four_pow_ceil_ne_top {κ : ℝ} (hκ : 0 < κ) :
    ∑' k : ℕ, ((4 : ℝ≥0∞) ^ ⌈κ * k⌉₊)⁻¹ ≠ ⊤ := by
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set r : ℝ := Real.exp (-(κ * Real.log 4)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith)
  have key : ∀ k : ℕ, ((4 : ℝ≥0∞) ^ ⌈κ * k⌉₊)⁻¹ ≤ (ENNReal.ofReal r) ^ k := by
    intro k
    have h4 : (4 : ℝ≥0∞) ^ ⌈κ * k⌉₊ = ENNReal.ofReal ((4 : ℝ) ^ ⌈κ * k⌉₊) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num
    rw [h4, ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow hr0]
    apply ENNReal.ofReal_le_ofReal
    have e4 : (4 : ℝ) ^ ⌈κ * k⌉₊ = Real.exp (⌈κ * k⌉₊ * Real.log 4) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e4, ← Real.exp_neg, hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have := Nat.le_ceil (κ * k)
    nlinarith
  have hgeo : ∑' k : ℕ, (ENNReal.ofReal r) ^ k ≠ ⊤ := by
    rw [ENNReal.tsum_geometric, Ne, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le]
    exact (ENNReal.ofReal_lt_one).2 hr1
  exact ne_top_of_le_ne_top hgeo (ENNReal.tsum_le_tsum key)

/-- **Double series for a linearly growing shift.** If `∑ₙ 4ⁿ p n < ∞` and `κ > 0`, then
`∑ₖ ∑ₙ 4ⁿ p (n + ⌈κ k⌉₊) < ∞`. -/
theorem tsum_tsum_four_pow_mul_ceil_shift_ne_top {p : ℕ → ℝ≥0∞} {κ : ℝ}
    (hp : ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p n ≠ ⊤) (hκ : 0 < κ) :
    ∑' k : ℕ, ∑' n : ℕ, (4 : ℝ≥0∞) ^ n * p (n + ⌈κ * k⌉₊) ≠ ⊤ :=
  tsum_tsum_four_pow_mul_shift_ne_top hp (tsum_inv_four_pow_ceil_ne_top hκ)

end LatticeProb
