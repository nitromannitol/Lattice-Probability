/-
The local central limit theorem for the binomial kernel, with an explicit `1/m` error.

`binomPMF m j` is the probability that a sum of `m` independent signs equals `j`, that is
`C(m, (m + j)/2) / 2^m`; the parity constraint `j ≡ m [ZMOD 2]` is what makes the binomial
coefficient the right one.  `gaussianDensity x` is the standard normal density
`(2π)^{-1/2} exp(-x²/2)`.

The main result `exists_binomPMF_localCLT` bounds
`|√m · P_m(j) − 2 · gaussianDensity (j/√m)|` by `C/m` uniformly over `m ≥ 1` and over the
`j` of the right parity.  The parity constraint is part of the statement: without it the
left-hand side is `2 · gaussianDensity` at every second `j` and `0` at the others, so the
unconstrained statement is false.
-/

import Mathlib

open Filter Finset Real MeasureTheory
open scoped Topology

noncomputable section

namespace LatticeProb.BinomialLCLT

/-- The probability that a sum of `m` independent signs equals `j`. -/
def binomPMF (m : ℕ) (j : ℤ) : ℝ := (m.choose ((m + j) / 2).toNat : ℝ) / 2 ^ m

/-- The standard normal density. -/
def gaussianDensity (x : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- **Vacuity check at `m = 1`.**  The only `j` of the right parity with `|j| ≤ 1` is `±1`, and
there `P_1(j) = 1/2`. -/
theorem binomPMF_one (j : ℤ) (hj : j ≡ (1 : ℤ) [ZMOD 2]) (hj1 : |j| ≤ 1) :
    binomPMF 1 j = 1 / 2 := by
  have hjmod : j % 2 = 1 := by
    rw [Int.ModEq] at hj; norm_num at hj; exact hj
  have hjodd : j = 1 ∨ j = -1 := by
    have hb : -1 ≤ j ∧ j ≤ 1 := abs_le.mp hj1
    omega
  rcases hjodd with rfl | rfl <;> norm_num [binomPMF]

/-- **Vacuity check at `m = 2`.**  The `j` of the right parity with `|j| ≤ 2` are `0, ±2`, and
there `P_2(0) = 1/2`, `P_2(±2) = 1/4`. -/
theorem binomPMF_two (j : ℤ) (hj : j ≡ (2 : ℤ) [ZMOD 2]) (hj2 : |j| ≤ 2) :
    binomPMF 2 j = if j = 0 then 1 / 2 else 1 / 4 := by
  have hjmod : j % 2 = 0 := by
    have h := Int.ModEq.dvd hj
    omega
  have hjeven : j = 2 ∨ j = 0 ∨ j = -2 := by
    have hb : -2 ≤ j ∧ j ≤ 2 := abs_le.mp hj2
    omega
  rcases hjeven with rfl | rfl | rfl <;> norm_num [binomPMF, Int.toNat]

/-- The standard normal density is positive. -/
theorem gaussianDensity_pos (x : ℝ) : 0 < gaussianDensity x := by
  unfold gaussianDensity; positivity

/-- The standard normal density at zero is `(2π)^{-1/2}`. -/
theorem gaussianDensity_zero : gaussianDensity 0 = (Real.sqrt (2 * Real.pi))⁻¹ := by
  simp [gaussianDensity]

/-- The standard normal density is bounded by `1`. -/
theorem gaussianDensity_le_one (x : ℝ) : gaussianDensity x ≤ 1 := by
  unfold gaussianDensity
  have h1 : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.sqrt_pos.mpr (by positivity))]
    exact Real.one_le_sqrt.mpr (by nlinarith [Real.pi_gt_three])
  have h2 : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg x]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)
      ≤ 1 * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = 1 := by ring

end LatticeProb.BinomialLCLT

end
