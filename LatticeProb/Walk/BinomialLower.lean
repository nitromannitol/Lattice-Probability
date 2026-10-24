import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A Gaussian lower bound for binomial probabilities

Uniform Stirling bounds and the elementary entropy bound by the chi-square divergence give
an estimate at every binomial index, including the two endpoints. The displacement is `2j - n`.
-/

namespace LatticeProb

/-- The logarithm of the Stirling sequence lies between zero and one at positive indices. -/
lemma log_stirlingSeq_mem {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (Stirling.stirlingSeq n) ∧
      Real.log (Stirling.stirlingSeq n) ≤ 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hl := Stirling.log_stirlingSeq_bounded_by_constant m
  have hu := Stirling.log_stirlingSeq'_antitone (Nat.zero_le m)
  change Real.log (Stirling.stirlingSeq (m + 1)) ≤
    Real.log (Stirling.stirlingSeq 1) at hu
  rw [Stirling.stirlingSeq_one, Real.log_div (by positivity) (by positivity),
    Real.log_exp, Real.log_sqrt (by norm_num)] at hu
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hnonneg := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  constructor <;> linarith

/-- Coarse two-sided logarithmic Stirling estimates, sufficient for uniform binomial bounds. -/
lemma log_factorial_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + Real.log n / 2 ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤
        (n : ℝ) * Real.log n - n + Real.log n / 2 + 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) (ne_of_gt hnpos),
    Real.log_div (ne_of_gt hnpos) (ne_of_gt (Real.exp_pos 1)), Real.log_exp] at h
  obtain ⟨hl, hu⟩ := log_stirlingSeq_mem hn
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hnonneg := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  constructor <;> linarith

/-- The binary relative entropy is bounded above by its chi-square divergence. -/
lemma binomial_entropy_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : t = a + b) :
    a * Real.log a + b * Real.log b - t * Real.log t + t * Real.log 2 ≤
      (2 * a - t) ^ 2 / t := by
  have htpos : 0 < t := by linarith
  have hla := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * a / t)
  have hlb := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * b / t)
  rw [Real.log_div (by positivity) (ne_of_gt htpos),
    Real.log_mul (by norm_num) (ne_of_gt ha)] at hla
  rw [Real.log_div (by positivity) (ne_of_gt htpos),
    Real.log_mul (by norm_num) (ne_of_gt hb)] at hlb
  have hal := mul_le_mul_of_nonneg_left hla ha.le
  have hbl := mul_le_mul_of_nonneg_left hlb hb.le
  have hid : a * (2 * a / t - 1) + b * (2 * b / t - 1) =
      (2 * a - t) ^ 2 / t := by
    field_simp
    rw [ht]
    ring
  calc
    _ = a * (Real.log 2 + Real.log a - Real.log t) +
        b * (Real.log 2 + Real.log b - Real.log t) := by rw [ht]; ring
    _ ≤ a * (2 * a / t - 1) + b * (2 * b / t - 1) := add_le_add hal hbl
    _ = _ := hid

/-- A logarithmic Gaussian lower estimate, valid at every binomial index. -/
lemma log_choose_div_two_pow_lower (n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    -4 - Real.log n / 2 - (2 * (j : ℝ) - n) ^ 2 / n ≤
      Real.log ((Nat.choose n j : ℝ) / 2 ^ n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcpos : (0 : ℝ) < Nat.choose n j := by exact_mod_cast Nat.choose_pos hj
  have hlog : Real.log ((Nat.choose n j : ℝ) / 2 ^ n) =
      Real.log (Nat.choose n j : ℝ) - (n : ℝ) * Real.log 2 := by
    rw [Real.log_div (ne_of_gt hcpos) (by positivity), Real.log_pow]
  have hlogn := Real.log_natCast_nonneg n
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rcases eq_or_lt_of_le (Nat.zero_le j) with hjzero | hjpos
  · subst j
    rw [hlog, Nat.choose_zero_right, Nat.cast_one, Real.log_one]
    have hid : (2 * (0 : ℝ) - n) ^ 2 / n = n := by field_simp; ring
    simp only [Nat.cast_zero]
    rw [hid]
    nlinarith
  rcases eq_or_lt_of_le hj with hjeq | hjlt
  · subst j
    rw [hlog, Nat.choose_self, Nat.cast_one, Real.log_one]
    have hid : (2 * (n : ℝ) - n) ^ 2 / n = n := by field_simp; ring
    rw [hid]
    nlinarith
  have hlpos : 1 ≤ n - j := by omega
  have hjone : 1 ≤ j := hjpos
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hlR : (0 : ℝ) < n - j := sub_pos.mpr (by exact_mod_cast hjlt)
  have hsub : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := Nat.cast_sub hj
  have hfac := Nat.choose_mul_factorial_mul_factorial hj
  have hfacR : (Nat.choose n j : ℝ) * (j.factorial : ℝ) *
      ((n - j).factorial : ℝ) = (n.factorial : ℝ) := by exact_mod_cast hfac
  have hfaclog := congrArg Real.log hfacR
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hcpos) (by positivity)] at hfaclog
  have hnlo := (log_factorial_bounds hn).1
  have hjup := (log_factorial_bounds hjone).2
  have hlup := (log_factorial_bounds hlpos).2
  rw [hsub] at hlup
  have he := binomial_entropy_le hjR hlR (by ring :
    (n : ℝ) = (j : ℝ) + ((n : ℝ) - j))
  have hjlog : Real.log (j : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hjR (by exact_mod_cast hj)
  have hllog : Real.log ((n : ℝ) - j) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hlR (by linarith [Nat.cast_nonneg (α := ℝ) j])
  rw [hlog]
  linarith

/-- Every binomial probability has a uniform Gaussian lower bound with displacement `2j - n`. -/
theorem choose_mul_two_pow_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (n j : ℕ), 1 ≤ n → j ≤ n →
      c * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(2 * (j : ℝ) - n) ^ 2 / (c * n)) ≤
        (Nat.choose n j : ℝ) / 2 ^ n := by
  refine ⟨Real.exp (-4), Real.exp_pos _, ?_⟩
  intro n j hn hj
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hc : Real.exp (-4 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hden : Real.exp (-4 : ℝ) * n ≤ n := by nlinarith
  have hquot : (2 * (j : ℝ) - n) ^ 2 / n ≤
      (2 * (j : ℝ) - n) ^ 2 / (Real.exp (-4) * n) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
  have hlog := log_choose_div_two_pow_lower n j hn hj
  have hp : (0 : ℝ) < (Nat.choose n j : ℝ) / 2 ^ n := by
    exact div_pos (by exact_mod_cast Nat.choose_pos hj) (by positivity)
  rw [Real.rpow_def_of_pos hnpos, ← Real.exp_add, ← Real.exp_add]
  apply (Real.le_log_iff_exp_le hp).mp
  simp only [neg_div]
  linarith

end LatticeProb
