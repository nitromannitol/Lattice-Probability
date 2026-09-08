/-
The Stirling normalization of the central binomial coefficient.

`C(2m,m)/4^m` is `stirlingSeq (2m) / (stirlingSeq m ^ 2 √m)` exactly, by writing
each factorial through Mathlib's `Stirling.stirlingSeq`, and the two Stirling
sequences converge to `√π`, so `C(2m,m)/4^m · √(πm) → 1`.

Together with the binomial form of the one-dimensional kernel this is the
normalization of the one-dimensional local limit theorem: the ratio
`C(2m,m+k)/C(2m,m)` is handled without Stirling in `LatticeProb.Walk.BinomRatio`,
and the peak value is handled here.
-/
import LatticeProb.Walk.SRWOneDim
import Mathlib.Analysis.SpecialFunctions.Stirling

noncomputable section

namespace LatticeProb

open Real

theorem centralBinom_eq_stirling {m : ℕ} (hm : 1 ≤ m) :
    (Nat.choose (2 * m) m : ℝ) / 4 ^ m
      = Stirling.stirlingSeq (2 * m) / (Stirling.stirlingSeq m ^ 2 * Real.sqrt m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hSm : Stirling.stirlingSeq m ≠ 0 := by
    have := Stirling.sqrt_pi_le_stirlingSeq (n := m) (by omega)
    have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    linarith
  have hsq2m : Real.sqrt (2 * ((2 * m : ℕ) : ℝ)) = 2 * Real.sqrt ((m : ℕ) : ℝ) := by
    rw [show (2 : ℝ) * ((2 * m : ℕ) : ℝ) = 4 * (m : ℝ) by push_cast; ring,
      show (4 : ℝ) * (m : ℝ) = 2 ^ 2 * (m : ℝ) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hpow : (((2 * m : ℕ) : ℝ) / Real.exp 1) ^ (2 * m)
      = 4 ^ m * ((((m : ℕ) : ℝ) / Real.exp 1) ^ m) ^ 2 := by
    rw [show (((2 * m : ℕ) : ℝ) / Real.exp 1) = 2 * (((m : ℕ) : ℝ) / Real.exp 1) by
      push_cast; ring]
    rw [mul_pow, show 2 * m = m * 2 by ring, pow_mul, pow_mul]
    congr 1
    rw [← pow_mul, mul_comm m 2, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
  have hfac2 : (Nat.factorial (2 * m) : ℝ)
      = Stirling.stirlingSeq (2 * m) * Real.sqrt (2 * ((2 * m : ℕ) : ℝ))
        * (((2 * m : ℕ) : ℝ) / Real.exp 1) ^ (2 * m) := by
    rw [Stirling.stirlingSeq]
    field_simp
  have hfac1 : (Nat.factorial m : ℝ)
      = Stirling.stirlingSeq m * Real.sqrt (2 * ((m : ℕ) : ℝ))
        * ((((m : ℕ) : ℝ)) / Real.exp 1) ^ m := by
    rw [Stirling.stirlingSeq]
    field_simp
  have hchoose : (Nat.choose (2 * m) m : ℝ) * (Nat.factorial m : ℝ) * (Nat.factorial m : ℝ)
      = (Nat.factorial (2 * m) : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left m (by norm_num : 0 < 2))
    rw [show 2 * m - m = m by omega] at h
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) h
  set r : ℝ := Real.sqrt ((m : ℕ) : ℝ) with hr
  set y : ℝ := (((m : ℕ) : ℝ) / Real.exp 1) ^ m with hy
  have hrpos : 0 < r := Real.sqrt_pos.mpr hm0
  have hypos : 0 < y := by rw [hy]; positivity
  have hmm : r * r = (m : ℝ) := Real.mul_self_sqrt (le_of_lt hm0)
  have hqq : Real.sqrt (2 * ((m : ℕ) : ℝ)) * Real.sqrt (2 * ((m : ℕ) : ℝ)) = 2 * (m : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hfac1sq : (Nat.factorial m : ℝ) * (Nat.factorial m : ℝ)
      = Stirling.stirlingSeq m ^ 2 * (2 * (m : ℝ)) * y ^ 2 := by
    rw [hfac1]
    linear_combination (Stirling.stirlingSeq m ^ 2 * y ^ 2) * hqq
  have hchoose' : (Nat.choose (2 * m) m : ℝ) * (Stirling.stirlingSeq m ^ 2 * (2 * (m : ℝ)) * y ^ 2)
      = Stirling.stirlingSeq (2 * m) * (2 * r) * (4 ^ m * y ^ 2) := by
    rw [← hfac1sq, ← mul_assoc]
    rw [hchoose, hfac2, hsq2m, hpow]
  have hden : Stirling.stirlingSeq m ^ 2 * r ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero 2 hSm) (ne_of_gt hrpos)
  rw [div_eq_div_iff (by positivity) hden]
  refine mul_right_cancel₀ (b := 2 * r * y ^ 2) (by positivity) ?_
  linear_combination hchoose' + (2 * (Nat.choose (2 * m) m : ℝ) * Stirling.stirlingSeq m ^ 2 * y ^ 2) * hmm

/-- **The Stirling normalization of the one-dimensional kernel.**
`C(2m,m)/4^m · √(πm) → 1`. -/
theorem tendsto_centralBinom_mul_sqrt :
    Filter.Tendsto (fun m : ℕ => (Nat.choose (2 * m) m : ℝ) / 4 ^ m * Real.sqrt (Real.pi * m))
      Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun m : ℕ => Stirling.stirlingSeq (2 * m)) Filter.atTop
      (nhds (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have h2 : Filter.Tendsto (fun m : ℕ => Stirling.stirlingSeq m ^ 2) Filter.atTop
      (nhds Real.pi) := by
    have h := Stirling.tendsto_stirlingSeq_sqrt_pi.pow 2
    rwa [Real.sq_sqrt Real.pi_pos.le] at h
  have hlim : Filter.Tendsto
      (fun m : ℕ => Stirling.stirlingSeq (2 * m) * Real.sqrt Real.pi / Stirling.stirlingSeq m ^ 2)
      Filter.atTop (nhds 1) := by
    have h := (h1.mul (tendsto_const_nhds (x := Real.sqrt Real.pi))).div h2 Real.pi_ne_zero
    rwa [show Real.sqrt Real.pi * Real.sqrt Real.pi / Real.pi = 1 from by
      rw [Real.mul_self_sqrt Real.pi_pos.le]; exact div_self Real.pi_ne_zero] at h
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hSm : Stirling.stirlingSeq m ≠ 0 := by
    have h := Stirling.sqrt_pi_le_stirlingSeq (n := m) (by omega)
    have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    intro hc
    rw [hc] at h
    linarith
  have hrne : Real.sqrt ((m : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm0)
  rw [centralBinom_eq_stirling hm, Real.sqrt_mul Real.pi_pos.le]
  field_simp

/-! ### The kernel at an even time and an even site -/

/-- The one-dimensional kernel at an even time and an even site is the central
binomial coefficient shifted by `k`. -/
theorem srwHeat_one_two_mul_binom (m k : ℕ) (hk : k ≤ m) :
    srwHeat 1 (2 * m) ![2 * (k : ℤ)] = (Nat.choose (2 * m) (m + k) : ℝ) / 4 ^ m := by
  have h := srwHeat_one_binom (2 * m) (m + k) (m - k) (by omega)
  rw [show ((m + k : ℕ) : ℤ) - ((m - k : ℕ) : ℤ) = 2 * (k : ℤ) from by
    rw [Nat.cast_sub hk]; push_cast; ring] at h
  rw [h, show (2 : ℝ) ^ (2 * m) = 4 ^ m from by
    rw [pow_mul, show (2 : ℝ) ^ 2 = 4 from by norm_num]]

end LatticeProb
