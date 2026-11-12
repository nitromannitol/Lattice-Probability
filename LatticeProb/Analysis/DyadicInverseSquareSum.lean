import Mathlib

/-!
# Inverse-square sums from a quadratic count bound

Let `T` be a finite family with nonnegative weights `a k` and distances `t k ∈ [s, R)` from a pole.
If the weight carried by the indices at distance `< r` is at most `A r²` for every `r ∈ [s, 2R]`
(a quadratic "mass" bound for the discs around the pole), then the inverse-square sum
`∑ k, a k / (t k)²` is at most `4 A (log₂ (R / s) + 1)`: the sum is a logarithm of the ratio of the
outer and inner scales. The proof splits the indices into dyadic shells `2^j s ≤ t k < 2^(j+1) s`.

## Main results

* `LatticeProb.sum_div_sq_le_of_quadratic_count`: the bound above.
* `LatticeProb.sum_div_sq_le_log_of_quadratic_count`: with `s ≤ 1 / 4` and `R ≤ 2`, the bound
  `18 A log (1 / s)`.
-/

open Finset

namespace LatticeProb

/-- The dyadic shell index of a distance `t ≥ s > 0`. -/
private theorem shell_bounds {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    (2 : ℝ) ^ ⌊Real.logb 2 (t / s)⌋₊ * s ≤ t ∧ t < (2 : ℝ) ^ (⌊Real.logb 2 (t / s)⌋₊ + 1) * s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hts : 0 < t / s := div_pos ht hs
  have h0 : 0 ≤ Real.logb 2 (t / s) :=
    Real.logb_nonneg (by norm_num) ((one_le_div hs).2 hst)
  constructor
  · have h1 : ((⌊Real.logb 2 (t / s)⌋₊ : ℕ) : ℝ) ≤ Real.logb 2 (t / s) := Nat.floor_le h0
    have h2 := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hts).1 h1
    rw [Real.rpow_natCast] at h2
    rwa [le_div_iff₀ hs] at h2
  · have h1 : Real.logb 2 (t / s) < (⌊Real.logb 2 (t / s)⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
    have h2 := (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hts).1 h1
    rw [show (((⌊Real.logb 2 (t / s)⌋₊ : ℕ) : ℝ) + 1) = ((⌊Real.logb 2 (t / s)⌋₊ + 1 : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_natCast] at h2
    rwa [div_lt_iff₀ hs] at h2

/-- **Inverse-square sum from a quadratic count bound.** If `t k ∈ [s, R)` for every index of the
finite family `T`, and the weight of the indices with `t k < r` is at most `A r²` for all
`r ∈ [s, 2R]`, then `∑ k ∈ T, a k / (t k)² ≤ 4 A (log₂ (R / s) + 1)`. -/
theorem sum_div_sq_le_of_quadratic_count {ι : Type*} (T : Finset ι) (a t : ι → ℝ)
    (ha : ∀ k ∈ T, 0 ≤ a k) {s R A : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (ht : ∀ k ∈ T, s ≤ t k ∧ t k < R)
    (hcount : ∀ r : ℝ, s ≤ r → r ≤ 2 * R → ∑ k ∈ T with t k < r, a k ≤ A * r ^ 2) :
    ∑ k ∈ T, a k / t k ^ 2 ≤ 4 * A * (Real.logb 2 (R / s) + 1) := by
  classical
  have hA : 0 ≤ A := by
    have := hcount s le_rfl (by linarith)
    have h0 : 0 ≤ ∑ k ∈ T with t k < s, a k := sum_nonneg fun k hk => ha k (mem_filter.1 hk).1
    nlinarith [sq_nonneg s, mul_pos hs hs]
  have hRs : 1 ≤ R / s := (one_le_div hs).2 hsR
  have hlog : 0 ≤ Real.logb 2 (R / s) := Real.logb_nonneg (by norm_num) hRs
  set J : ℕ := ⌊Real.logb 2 (R / s)⌋₊ + 1 with hJ
  -- the shell index of each index
  set j : ι → ℕ := fun k => ⌊Real.logb 2 (t k / s)⌋₊ with hj
  have hjJ : ∀ k ∈ T, j k ∈ range J := by
    intro k hk
    obtain ⟨h1, h2⟩ := ht k hk
    have htk : 0 < t k / s := div_pos (lt_of_lt_of_le hs h1) hs
    have : Real.logb 2 (t k / s) ≤ Real.logb 2 (R / s) :=
      Real.logb_le_logb_of_le (by norm_num) htk
        (div_le_div_of_nonneg_right h2.le hs.le)
    rw [mem_range, hJ]
    exact Nat.lt_succ_of_le (Nat.floor_le_floor this)
  rw [← sum_fiberwise_of_maps_to hjJ]
  have hshell : ∀ i ∈ range J, ∑ k ∈ T with j k = i, a k / t k ^ 2 ≤ 4 * A := by
    intro i hi
    have hiJ : i ≤ ⌊Real.logb 2 (R / s)⌋₊ := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have hile : (i : ℝ) ≤ Real.logb 2 (R / s) :=
      (Nat.cast_le.2 hiJ).trans (Nat.floor_le hlog)
    have h2i : (2 : ℝ) ^ i ≤ R / s := by
      have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by linarith)).1 hile
      rwa [Real.rpow_natCast] at this
    have hpos : 0 < (2 : ℝ) ^ i * s := by positivity
    have hr1 : s ≤ (2 : ℝ) ^ (i + 1) * s := by
      have : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hr2 : (2 : ℝ) ^ (i + 1) * s ≤ 2 * R := by
      have h3 : (2 : ℝ) ^ i * s ≤ R := by rwa [le_div_iff₀ hs] at h2i
      rw [pow_succ]; nlinarith
    have hsub : ∀ k ∈ T.filter (fun k => j k = i), a k / t k ^ 2 ≤ a k / ((2 : ℝ) ^ i * s) ^ 2 ∧
        t k < (2 : ℝ) ^ (i + 1) * s := by
      intro k hk
      obtain ⟨hkT, hki⟩ := mem_filter.1 hk
      obtain ⟨hb1, hb2⟩ := shell_bounds hs (ht k hkT).1
      have e : ⌊Real.logb 2 (t k / s)⌋₊ = i := hki
      rw [e] at hb1 hb2
      have hb1' : (2 : ℝ) ^ i * s ≤ t k := hb1
      have hb2' : t k < (2 : ℝ) ^ (i + 1) * s := hb2
      refine ⟨?_, hb2'⟩
      exact div_le_div_of_nonneg_left (ha k hkT) (by positivity)
        (pow_le_pow_left₀ hpos.le hb1' 2)
    calc ∑ k ∈ T with j k = i, a k / t k ^ 2
        ≤ ∑ k ∈ T with j k = i, a k / ((2 : ℝ) ^ i * s) ^ 2 :=
          sum_le_sum fun k hk => (hsub k hk).1
      _ ≤ ∑ k ∈ T with t k < (2 : ℝ) ^ (i + 1) * s, a k / ((2 : ℝ) ^ i * s) ^ 2 := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun k hk _ => ?_
          · intro k hk
            exact mem_filter.2 ⟨(mem_filter.1 hk).1, (hsub k hk).2⟩
          · exact div_nonneg (ha k (mem_filter.1 hk).1) (by positivity)
      _ = (∑ k ∈ T with t k < (2 : ℝ) ^ (i + 1) * s, a k) / ((2 : ℝ) ^ i * s) ^ 2 := by
          rw [sum_div]
      _ ≤ (A * ((2 : ℝ) ^ (i + 1) * s) ^ 2) / ((2 : ℝ) ^ i * s) ^ 2 :=
          div_le_div_of_nonneg_right (hcount _ hr1 hr2) (by positivity)
      _ = 4 * A := by
          rw [pow_succ]; field_simp; ring
  calc ∑ i ∈ range J, ∑ k ∈ T with j k = i, a k / t k ^ 2
      ≤ ∑ _i ∈ range J, 4 * A := sum_le_sum hshell
    _ = 4 * A * J := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ 4 * A * (Real.logb 2 (R / s) + 1) := by
          have : (J : ℝ) ≤ Real.logb 2 (R / s) + 1 := by
            rw [hJ]; push_cast
            linarith [Nat.floor_le hlog]
          exact mul_le_mul_of_nonneg_left this (by positivity)

/-- With `s ≤ 1 / 4` and `R ≤ 2`, the dyadic bound is `18 A log (1 / s)`. -/
theorem sum_div_sq_le_log_of_quadratic_count {ι : Type*} (T : Finset ι) (a t : ι → ℝ)
    (ha : ∀ k ∈ T, 0 ≤ a k) {s R A : ℝ} (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hR : R ≤ 2)
    (hsR : s ≤ R) (ht : ∀ k ∈ T, s ≤ t k ∧ t k < R)
    (hcount : ∀ r : ℝ, s ≤ r → r ≤ 2 * R → ∑ k ∈ T with t k < r, a k ≤ A * r ^ 2) :
    ∑ k ∈ T, a k / t k ^ 2 ≤ 18 * A * Real.log (1 / s) := by
  have h := sum_div_sq_le_of_quadratic_count T a t ha hs hsR ht hcount
  have hA : 0 ≤ A := by
    have := hcount s le_rfl (by linarith)
    have h0 : 0 ≤ ∑ k ∈ T with t k < s, a k := sum_nonneg fun k hk => ha k (mem_filter.1 hk).1
    nlinarith [sq_nonneg s, mul_pos hs hs]
  refine h.trans ?_
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hRs : R / s ≤ 2 / s := div_le_div_of_nonneg_right hR hs.le
  have hRs0 : 0 < R / s := div_pos (lt_of_lt_of_le hs hsR) hs
  have hlogb : Real.logb 2 (R / s) ≤ Real.logb 2 (2 / s) :=
    Real.logb_le_logb_of_le (by norm_num) hRs0 hRs
  have h1s : (4 : ℝ) ≤ 1 / s := by
    rw [le_div_iff₀ hs]; linarith
  have hlog4 : Real.log 4 ≤ Real.log (1 / s) := Real.log_le_log (by norm_num) h1s
  have hlog4' : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog2s : Real.logb 2 (2 / s) = (Real.log 2 + Real.log (1 / s)) / Real.log 2 := by
    rw [Real.logb, show (2 : ℝ) / s = 2 * (1 / s) by field_simp,
      Real.log_mul (by norm_num) (by positivity)]
  have hbound : Real.logb 2 (R / s) + 1 ≤ 3 * Real.log (1 / s) / Real.log 2 := by
    have : Real.logb 2 (R / s) + 1 ≤ (Real.log 2 + Real.log (1 / s)) / Real.log 2 + 1 := by
      linarith
    refine this.trans ?_
    rw [div_add_one hl2.ne', div_le_div_iff_of_pos_right hl2]
    linarith
  have hlog2gt : 2 / 3 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  calc 4 * A * (Real.logb 2 (R / s) + 1)
      ≤ 4 * A * (3 * Real.log (1 / s) / Real.log 2) :=
        mul_le_mul_of_nonneg_left hbound (by linarith)
    _ ≤ 4 * A * (3 * Real.log (1 / s) / (2 / 3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        have hL : 0 ≤ Real.log (1 / s) := Real.log_nonneg (by linarith)
        exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hlog2gt
    _ = 18 * A * Real.log (1 / s) := by ring

end LatticeProb
