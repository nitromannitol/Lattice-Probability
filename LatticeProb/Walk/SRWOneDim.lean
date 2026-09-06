/-
The one-dimensional simple random walk kernel against the lazy one.

Two steps of the simple walk on `ℤ` make one step of the lazy walk on `2ℤ`:
the pair of increments `±1, ±1` sums to `0` with probability `1/2` and to `±2`
with probability `1/4` each.  So the simple kernel at an even time and an even
site is the lazy kernel of `LatticeProb/Walk/OneDim.lean`, and every bound
proved there transfers.  The consequence recorded here is the sup bound
`P^n(0, k) ≤ √2 / √(n+1)`, which has no parity restriction because at the times
and sites where the parity fails the kernel is zero.
-/
import Mathlib
import LatticeProb.Walk.SRW
import LatticeProb.Walk.OneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

/-- The `ℓ¹` norm of a one-dimensional site is the absolute value. -/
theorem graphNorm_one (a : ℤ) : graphNorm (![a] : Site 1) = a.natAbs := by
  simp [graphNorm]

/-- The simple walk at an even time and an even site is the lazy walk. -/
theorem srwHeat_one_two_mul (m : ℕ) (k : ℤ) :
    srwHeat 1 (2 * m) ![2 * k] = P1 m k := by
  induction m generalizing k with
  | zero =>
      rw [P1_zero_step]
      simp only [Nat.mul_zero]
      by_cases hk : k = 0
      · subst hk
        norm_num
        funext i
        exact i.elim0
      · rw [if_neg hk, srwHeat_zero, if_neg]
        intro hc
        apply hk
        have : (![2 * k] : Site 1) 0 = (0 : Site 1) 0 := by rw [hc]
        simp at this
        omega
  | succ m ih =>
      have hstep : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [hstep, srwHeat_one_succ, srwHeat_one_succ, srwHeat_one_succ]
      have e1 : 2 * k - 1 - 1 = 2 * (k - 1) := by ring
      have e2 : 2 * k - 1 + 1 = 2 * k := by ring
      have e3 : 2 * k + 1 - 1 = 2 * k := by ring
      have e4 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [e1, e2, e3, e4, ih, ih, ih]
      rw [P1_succ]
      ring

/-- At an even time the kernel is bounded by the peak of the lazy kernel. -/
theorem srwHeat_one_even_le (m : ℕ) (j : ℤ) :
    srwHeat 1 (2 * m) ![j] ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
  rcases Int.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hj : j = 2 * k := by omega
    subst hj
    calc srwHeat 1 (2 * m) ![2 * k] = P1 m k := srwHeat_one_two_mul m k
      _ ≤ P1 m 0 := P1_le_max m k
      _ ≤ 1 / Real.sqrt ((m : ℝ) + 1) := P1_zero_le_inv_sqrt m
  · have hzero : srwHeat 1 (2 * m) ![j] = 0 := by
      refine srwHeat_eq_zero_of_parity ?_
      rw [graphNorm_one]
      have hpar : ((j.natAbs : ℕ) : ZMod 2) = 1 := by
        rw [natAbs_cast_zmod, hk]
        push_cast
        ring_nf
        rw [show ((2 : ZMod 2)) = 0 by decide]
        ring
      have hpar2 : (((2 * m : ℕ)) : ZMod 2) = 0 := by
        push_cast
        rw [show ((2 : ZMod 2)) = 0 by decide]
        ring
      rw [hpar, hpar2]
      decide
    rw [hzero]
    positivity

/-- The sup bound on the one-dimensional simple kernel. -/
theorem srwHeat_one_le (n : ℕ) (j : ℤ) :
    srwHeat 1 n ![j] ≤ Real.sqrt 2 / Real.sqrt ((n : ℝ) + 1) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hn : n = 2 * m := by omega
    subst hn
    refine le_trans (srwHeat_one_even_le m j) ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Real.sqrt (((2 * m : ℕ) : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      push_cast
      ring_nf
      linarith
    linarith
  · have hn : n = 2 * m + 1 := by omega
    subst hn
    rw [srwHeat_one_succ]
    have hb1 := srwHeat_one_even_le m (j - 1)
    have hb2 := srwHeat_one_even_le m (j + 1)
    have hval : Real.sqrt 2 / Real.sqrt (((2 * m + 1 : ℕ) : ℝ) + 1)
        = 1 / Real.sqrt ((m : ℝ) + 1) := by
      have h2 : (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * ((m : ℝ) + 1) := by push_cast; ring
      rw [h2, Real.sqrt_mul (by norm_num)]
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [hval]
    linarith

end LatticeProb
