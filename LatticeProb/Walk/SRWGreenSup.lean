/-
The truncated Green function of the simple random walk on `ℤ^d`, dimension by
dimension.

`srwGreen d n x = ∑_{j < n} srwHeat d j x` is the expected number of visits to
`x` strictly before time `n` of the simple random walk started at the origin.
Summing the on-diagonal sup bound `LatticeProb.srwHeat_sup_bound`, which reads
`srwHeat d j x ≤ √2^d · C_d · j^{-d/2}`, over `1 ≤ j < n`, and bounding the
`j = 0` term by `1`, reduces every estimate to one of the three elementary
series bounds of `LatticeProb/Walk/Series.lean`.  The result is the simple-walk
counterpart of the lazy statements `LatticeProb.gR_one_dim_le`,
`LatticeProb.gR_two_dim_le` and `LatticeProb.gR_high_dim_le`: order `√n` in
`d = 1`, order `log n` in `d = 2`, and bounded uniformly in the horizon for
`d ≥ 3`.  The only difference from the lazy constants is the factor `√2^d`, one
factor of `√2` per coordinate coming from the parity of the one-dimensional
walk.
-/
import Mathlib
import LatticeProb.Walk.SRWDecomp
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.SRWSup
import LatticeProb.Walk.GreenBounds
import LatticeProb.Walk.Series

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### The truncated Green function, summed -/

/-- The constant of the simple-walk sup bound is nonnegative. -/
lemma srwGreenConst_nonneg (d : ℕ) : (0 : ℝ) ≤ Real.sqrt 2 ^ d * greenConst d :=
  mul_nonneg (by positivity) (greenConst_nonneg d)

/-- Summing the sup bound over `0 ≤ j < n`: the `j = 0` term is at most `1` and
every later term is at most `√2^d · C_d · j^{-d/2}`. -/
lemma srwGreen_le (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (x : Site d) :
    srwGreen d n x
      ≤ 1 + ∑ r ∈ Finset.Ico 1 n, Real.sqrt 2 ^ d * greenConst d * (r : ℝ) ^ (-(d : ℝ) / 2) := by
  have hsplit : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext t
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnot : (0 : ℕ) ∉ Finset.Ico 1 n := by simp
  have h0 : srwHeat d 0 x ≤ 1 := by
    rw [srwHeat_zero]
    split <;> norm_num
  have hrest : ∀ r ∈ Finset.Ico 1 n, srwHeat d r x
      ≤ Real.sqrt 2 ^ d * greenConst d * (r : ℝ) ^ (-(d : ℝ) / 2) := fun r hr =>
    srwHeat_sup_bound hd (Finset.mem_Ico.mp hr).1 x
  unfold srwGreen
  rw [hsplit, Finset.sum_insert hnot]
  exact add_le_add h0 (Finset.sum_le_sum hrest)

/-! ### `d = 1`: the truncated Green function is of order `√n` -/

/-- `G_n(0,x) ≤ 1 + 2 √2 C √n` in one dimension, with `C = greenConst 1`. -/
theorem srwGreen_one_dim_le (n : ℕ) (hn : 1 ≤ n) (x : Site 1) :
    srwGreen 1 n x ≤ 1 + 2 * (Real.sqrt 2 * greenConst 1) * Real.sqrt (n : ℝ) := by
  have hmain := srwGreen_le (d := 1) one_pos hn x
  have hterm : ∀ r ∈ Finset.Ico 1 n,
      Real.sqrt 2 ^ 1 * greenConst 1 * ((r : ℝ) ^ (-((1 : ℕ) : ℝ) / 2))
        = (Real.sqrt 2 * greenConst 1) * (Real.sqrt (r : ℝ))⁻¹ := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    rw [pow_one, show -((1 : ℕ) : ℝ) / 2 = -(1 / 2) by norm_num, Real.rpow_neg hrpos.le,
      ← Real.sqrt_eq_rpow]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hmain
  have hreindex : ∑ r ∈ Finset.Ico 1 n, (Real.sqrt (r : ℝ))⁻¹
      = ∑ k ∈ Finset.range (n - 1), (1 : ℝ) / Real.sqrt ((k : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_div]
    congr 2
    push_cast
    ring
  have hsum : ∑ r ∈ Finset.Ico 1 n, (Real.sqrt (r : ℝ))⁻¹ ≤ 2 * Real.sqrt (n : ℝ) := by
    rw [hreindex]
    refine (sum_inv_sqrt_le (n - 1)).trans ?_
    have : Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n 1)
    linarith
  have hg : (0 : ℝ) ≤ Real.sqrt 2 * greenConst 1 :=
    mul_nonneg (Real.sqrt_nonneg 2) (greenConst_nonneg 1)
  nlinarith [hmain, hsum, hg]

/-! ### `d = 2`: the truncated Green function is of order `log n` -/

/-- `G_n(0,x) ≤ 1 + 2 C (1 + log n)` in two dimensions, with `C = greenConst 2`. -/
theorem srwGreen_two_dim_le (n : ℕ) (hn : 1 ≤ n) (x : Site 2) :
    srwGreen 2 n x ≤ 1 + (Real.sqrt 2 ^ 2 * greenConst 2) * (1 + Real.log (n : ℝ)) := by
  have hmain := srwGreen_le (d := 2) (by norm_num) hn x
  have hterm : ∀ r ∈ Finset.Ico 1 n,
      Real.sqrt 2 ^ 2 * greenConst 2 * ((r : ℝ) ^ (-((2 : ℕ) : ℝ) / 2))
        = (Real.sqrt 2 ^ 2 * greenConst 2) * ((r : ℝ))⁻¹ := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    rw [show -((2 : ℕ) : ℝ) / 2 = -1 from by norm_num, Real.rpow_neg_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hmain
  have hg : (0 : ℝ) ≤ Real.sqrt 2 ^ 2 * greenConst 2 := srwGreenConst_nonneg 2
  nlinarith [hmain, sum_inv_le_one_add_log n, hg]

/-! ### `d ≥ 3`: the truncated Green function is bounded -/

/-- `G_n(0,x) ≤ 1 + 3 √2^d C` for every horizon in dimension `d ≥ 3`, with
`C = greenConst d`. -/
theorem srwGreen_high_dim_le (hd : 3 ≤ d) (n : ℕ) (hn : 1 ≤ n) (x : Site d) :
    srwGreen d n x ≤ 1 + 3 * (Real.sqrt 2 ^ d * greenConst d) := by
  have hd0 : 0 < d := by omega
  have hg : (0 : ℝ) ≤ Real.sqrt 2 ^ d * greenConst d := srwGreenConst_nonneg d
  have hmain := srwGreen_le hd0 hn x
  have hterm : ∀ r ∈ Finset.Ico 1 n,
      Real.sqrt 2 ^ d * greenConst d * ((r : ℝ) ^ (-(d : ℝ) / 2))
        ≤ Real.sqrt 2 ^ d * greenConst d * ((r : ℝ) ^ (-(3 : ℝ) / 2)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
    have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    refine mul_le_mul_of_nonneg_left ?_ hg
    refine Real.rpow_le_rpow_of_exponent_le hr1' ?_
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hsum : ∑ r ∈ Finset.Ico 1 n,
      Real.sqrt 2 ^ d * greenConst d * ((r : ℝ) ^ (-(d : ℝ) / 2))
        ≤ Real.sqrt 2 ^ d * greenConst d * 3 :=
    (Finset.sum_le_sum hterm).trans (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_rpow_three_halves_le n) hg)
  linarith [hmain, hsum]

end LatticeProb
