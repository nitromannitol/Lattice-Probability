import Mathlib
import LatticeProb.Walk.VarianceScale
import LatticeProb.Walk.SRWGreenSup
import LatticeProb.Walk.SRWGreenLower

/-!
# The two norms of the truncated Green function

For the truncated Green function `g_n(x) = ∑_{j<n} P^j(0, x)` of the simple random walk on
`ℤ^d` and `n ≥ 2`: `‖g_n‖₂ ≍ n^{3/4}, n^{1/2}, n^{1/4}, √(log n), 1` in dimensions
one, two, three, four and five upward (`exists_sqrt_tsum_srwGreen_sq_bounds`, the square root of
the variance scale of `LatticeProb.Walk.VarianceScale`), and
`max_x g_n(x) ≍ n^{1/2}, log n, 1` in dimensions one, two and three upward
(`exists_iSup_srwGreen_le`, `exists_le_iSup_srwGreen`, from the pointwise bounds of
`LatticeProb.Walk.SRWGreenSup` and `LatticeProb.Walk.SRWGreenLower`); together `greenNorms`, the
display `eq:green-norms` that the parking formalization quotes from Bou-Rabee and Panagiotis,
Section 3.1. The upper bound on the maximum goes through `ciSup_le`, which needs no boundedness,
so the junk value of an unbounded real supremum never enters.
-/

noncomputable section

namespace LatticeProb

variable {d : ℕ}

/-- The rate of `‖g_n‖₂`: `n^{3/4}`, `n^{1/2}`, `n^{1/4}`, `√(log n)` and `1` in dimensions
one, two, three, four and five upward. -/
def greenL2Rate (d : ℕ) (n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ ((3 : ℝ) / 4)
  else if d = 2 then (n : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 3 then (n : ℝ) ^ ((1 : ℝ) / 4)
  else if d = 4 then Real.sqrt (Real.log n)
  else 1

/-- The rate of `max_x g_n(x)`: `n^{1/2}`, `log n` and `1` in dimensions one, two and three
upward. -/
def greenMaxRate (d : ℕ) (n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 2 then Real.log n
  else 1

/-! ### The `ℓ²` norm -/

/-- The `ℓ²` rate is the square root of the variance scale:
`greenL2Rate d n = √(varianceRate d n)`. -/
theorem greenL2Rate_eq_sqrt_varianceRate (d n : ℕ) :
    greenL2Rate d n = Real.sqrt (varianceRate d n) := by
  unfold greenL2Rate varianceRate
  split_ifs with h1 h2 h3 h4
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  · rw [Real.sqrt_eq_rpow]
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  · rfl
  · rw [Real.sqrt_one]

/-- The `ℓ²` norm of the truncated Green function:
`‖g_n‖₂ ≍ n^{3/4}, n^{1/2}, n^{1/4}, √(log n), 1` in dimensions one, two, three,
four and five upward, for `n ≥ 2`. -/
theorem exists_sqrt_tsum_srwGreen_sq_bounds (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      c * greenL2Rate d n ≤ Real.sqrt (∑' x : Site d, srwGreen d n x ^ 2) ∧
        Real.sqrt (∑' x : Site d, srwGreen d n x ^ 2) ≤ C * greenL2Rate d n := by
  obtain ⟨c, C, hc, hC, hbound⟩ := exists_tsum_srwGreen_sq_bounds hd
  refine ⟨Real.sqrt c, Real.sqrt C, Real.sqrt_pos.mpr hc, Real.sqrt_pos.mpr hC, ?_⟩
  intro n hn
  obtain ⟨hlow, hup⟩ := hbound n hn
  constructor
  · rw [greenL2Rate_eq_sqrt_varianceRate, ← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hlow
  · rw [greenL2Rate_eq_sqrt_varianceRate, ← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt hup

/-! ### The maximum -/

/-- The maximum of the truncated Green function is at most a constant times `n^{1/2}`, `log n`
and `1` in dimensions one, two and three upward, for `n ≥ 2`. -/
theorem exists_iSup_srwGreen_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      (⨆ x : Site d, srwGreen d n x) ≤ C * greenMaxRate d n := by
  obtain rfl | rfl | h3 : d = 1 ∨ d = 2 ∨ 3 ≤ d := by omega
  · refine ⟨1 + 2 * (Real.sqrt 2 * greenConst 1), ?_, fun n hn => ?_⟩
    · have hK : 0 ≤ 2 * (Real.sqrt 2 * greenConst 1) :=
        mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg 2) (greenConst_nonneg 1))
      linarith
    · have hn1 : 1 ≤ n := by omega
      have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
      have hK : 0 ≤ 2 * (Real.sqrt 2 * greenConst 1) :=
        mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg 2) (greenConst_nonneg 1))
      have hbound : ∀ x : Site 1,
          srwGreen 1 n x ≤ (1 + 2 * (Real.sqrt 2 * greenConst 1)) * Real.sqrt (n : ℝ) := by
        intro x
        have h := srwGreen_one_dim_le n hn1 x
        nlinarith [h, hK, hsqrt1]
      rw [greenMaxRate, if_pos rfl, ← Real.sqrt_eq_rpow]
      exact ciSup_le hbound
  · let K : ℝ := Real.sqrt 2 ^ 2 * greenConst 2
    refine ⟨(1 + K) / Real.log 2 + K, ?_, fun n hn => ?_⟩
    · have hK : 0 ≤ K := srwGreenConst_nonneg 2
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    · have hn1 : 1 ≤ n := by omega
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogn : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
      have hK : 0 ≤ K := srwGreenConst_nonneg 2
      have hbound : ∀ x : Site 2,
          srwGreen 2 n x ≤ ((1 + K) / Real.log 2 + K) * Real.log (n : ℝ) := by
        intro x
        have h := srwGreen_two_dim_le n hn1 x
        have h1 : (1 + K) ≤ ((1 + K) / Real.log 2) * Real.log (n : ℝ) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          exact mul_le_mul_of_nonneg_left hlogn (by linarith)
        have h2 : 1 + K * (1 + Real.log (n : ℝ))
            ≤ ((1 + K) / Real.log 2 + K) * Real.log (n : ℝ) := by
          nlinarith [h1]
        calc srwGreen 2 n x ≤ 1 + K * (1 + Real.log (n : ℝ)) := h
          _ ≤ ((1 + K) / Real.log 2 + K) * Real.log (n : ℝ) := h2
      rw [greenMaxRate]; simp
      exact ciSup_le hbound
  · refine ⟨1 + 3 * (Real.sqrt 2 ^ d * greenConst d), ?_, fun n hn => ?_⟩
    · have hK : 0 ≤ Real.sqrt 2 ^ d * greenConst d := srwGreenConst_nonneg d
      positivity
    · have hn1 : 1 ≤ n := by omega
      have hbound : ∀ x : Site d,
          srwGreen d n x ≤ (1 + 3 * (Real.sqrt 2 ^ d * greenConst d)) * 1 := by
        intro x
        rw [mul_one]
        exact srwGreen_high_dim_le h3 n hn1 x
      rw [greenMaxRate]
      rw [if_neg (by omega : d ≠ 1), if_neg (by omega : d ≠ 2)]
      exact ciSup_le hbound

/-- The maximum of the truncated Green function is at least a constant times `n^{1/2}`, `log n`
and `1` in dimensions one, two and three upward, for `n ≥ 2`. -/
theorem exists_le_iSup_srwGreen (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      c * greenMaxRate d n ≤ ⨆ x : Site d, srwGreen d n x := by
  obtain rfl | rfl | h3 : d = 1 ∨ d = 2 ∨ 3 ≤ d := by omega
  · obtain ⟨c, hc, h⟩ := exists_le_srwGreen_sup_one_dim
    refine ⟨c, hc, fun n hn => ?_⟩
    rw [greenMaxRate, if_pos rfl, ← Real.sqrt_eq_rpow]
    exact h n (by omega)
  · obtain ⟨c, hc, h⟩ := exists_le_srwGreen_sup_two_dim
    refine ⟨c, hc, fun n hn => ?_⟩
    rw [greenMaxRate, if_neg (by norm_num), if_pos rfl]
    exact h n hn
  · obtain ⟨c, hc, h⟩ := exists_le_srwGreen_sup_high_dim d h3
    refine ⟨c, hc, fun n hn => ?_⟩
    rw [greenMaxRate, if_neg (by omega), if_neg (by omega), mul_one]
    exact h n (by omega)

/-! ### Both norms -/

/-- **The two norms of the truncated Green function** (Bou-Rabee and Panagiotis, Section 3.1):
`‖g_n‖₂ ≍ greenL2Rate d n` and `max_x g_n(x) ≍ greenMaxRate d n` for `n ≥ 2`,
each with its own pair of constants. -/
theorem greenNorms (hd : 1 ≤ d) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * greenL2Rate d n ≤ Real.sqrt (∑' x : Site d, srwGreen d n x ^ 2) ∧
          Real.sqrt (∑' x : Site d, srwGreen d n x ^ 2) ≤ C * greenL2Rate d n) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * greenMaxRate d n ≤ (⨆ x : Site d, srwGreen d n x) ∧
          (⨆ x : Site d, srwGreen d n x) ≤ C * greenMaxRate d n) := by
  obtain ⟨c', hc', hlow⟩ := exists_le_iSup_srwGreen hd
  obtain ⟨C', hC', hup⟩ := exists_iSup_srwGreen_le hd
  exact ⟨exists_sqrt_tsum_srwGreen_sq_bounds hd,
    ⟨c', C', hc', hC', fun n hn => ⟨hlow n hn, hup n hn⟩⟩⟩

end LatticeProb
