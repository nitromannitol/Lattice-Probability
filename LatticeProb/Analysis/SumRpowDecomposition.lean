import Mathlib

/-!
# A decomposition of a real power of a finite sum

For a finite family of nonnegative reals `x_i` and a real exponent `p` with
`0 < p ≤ N` for a natural number `N ≥ 1`, the power `(∑ x_i)^p` is the sum of the
powers `x_i^p` plus an error controlled by the cross terms of `(∑ x_i)^N`:

`(∑ x_i)^p ≤ ∑ x_i^p + ((∑ x_i)^N - ∑ x_i^N)^(p / N)`.

The proof uses only the subadditivity of `t ↦ t^s` for `0 < s ≤ 1`.
-/

open Finset

namespace LatticeProb.Analysis

/-- Subadditivity of `t ↦ t ^ q` on finite sums of nonnegative reals, `0 < q ≤ 1`. -/
theorem sum_rpow_le_sum_rpow_of_le_one {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ i ∈ s, x i) ^ q ≤ ∑ i ∈ s, x i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hq0.ne']
  | insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat]
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a t)
    have hxt : ∀ i ∈ t, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ t, x i := Finset.sum_nonneg hxt
    calc (x a + ∑ i ∈ t, x i) ^ q ≤ x a ^ q + (∑ i ∈ t, x i) ^ q :=
          Real.rpow_add_le_add_rpow hxa hsum hq0.le hq1
      _ ≤ x a ^ q + ∑ i ∈ t, x i ^ q := by gcongr; exact ih hxt

/-- The natural power of a finite sum of nonnegative reals dominates the sum of the powers. -/
theorem sum_pow_le_pow_sum' {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {N : ℕ} (hN : N ≠ 0) :
    ∑ i ∈ s, x i ^ N ≤ (∑ i ∈ s, x i) ^ N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_pow hN]
  | insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat]
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a t)
    have hxt : ∀ i ∈ t, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ t, x i := Finset.sum_nonneg hxt
    calc x a ^ N + ∑ i ∈ t, x i ^ N ≤ x a ^ N + (∑ i ∈ t, x i) ^ N := by gcongr; exact ih hxt
      _ ≤ (x a + ∑ i ∈ t, x i) ^ N := pow_add_pow_le hxa hsum hN

/-- **Decomposition of `(∑ x_i)^p`.** For `0 < p ≤ N` (`N ≥ 1` natural),
`(∑ x_i)^p ≤ ∑ x_i^p + ((∑ x_i)^N - ∑ x_i^N)^(p/N)`. -/
theorem sum_rpow_le_sum_rpow_add_cross {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) {N : ℕ} (hN : N ≠ 0) {p : ℝ} (hp0 : 0 < p) (hpN : p ≤ N) :
    (∑ i ∈ s, x i) ^ p ≤
      ∑ i ∈ s, x i ^ p + ((∑ i ∈ s, x i) ^ N - ∑ i ∈ s, x i ^ N) ^ (p / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  set S : ℝ := ∑ i ∈ s, x i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg hx
  set A : ℝ := ∑ i ∈ s, x i ^ N with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i hi => pow_nonneg (hx i hi) N
  have hB0 : 0 ≤ S ^ N - A := sub_nonneg.2 (sum_pow_le_pow_sum' s x hx hN)
  have hq0 : 0 < p / N := div_pos hp0 hNpos
  have hq1 : p / N ≤ 1 := (div_le_one hNpos).2 hpN
  have hSp : S ^ p = (S ^ N) ^ (p / N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]
    congr 1
    field_simp
  have hSN : S ^ N = A + (S ^ N - A) := by ring
  have hAq : A ^ (p / N) ≤ ∑ i ∈ s, x i ^ p := by
    calc A ^ (p / N) ≤ ∑ i ∈ s, (x i ^ N) ^ (p / N) :=
          sum_rpow_le_sum_rpow_of_le_one s (fun i => x i ^ N)
            (fun i hi => pow_nonneg (hx i hi) N) hq0 hq1
      _ = ∑ i ∈ s, x i ^ p := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hx i hi)]
          congr 1
          field_simp
  calc S ^ p = (A + (S ^ N - A)) ^ (p / N) := by rw [hSp, ← hSN]
    _ ≤ A ^ (p / N) + (S ^ N - A) ^ (p / N) := Real.rpow_add_le_add_rpow hA0 hB0 hq0.le hq1
    _ ≤ _ := by gcongr

end LatticeProb.Analysis
