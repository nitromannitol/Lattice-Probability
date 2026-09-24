/-
**General-purpose real-analysis and finite-sum lemmas for a triangular-array
characteristic-function CLT.**

This module involves no probability and no model-specific object. It collects the elementary
cosine bounds `1 - cos x ≤ x²/2` and `0 ≤ 1 - cos x`, the normalized-floor limit, and two
finite-sum rearrangements that a characteristic-function Taylor expansion of a one-dimensional
lazy random walk needs. All five lemmas are fully generic: none of them has any walk content.

Moved from Parking-Sharpness.
-/
import Mathlib

open Filter Topology

namespace LatticeProb.Scaling.WalkCLT

/-- **The sharp quadratic upper bound `1 - cos x ≤ x²/2`.** -/
theorem one_sub_cos_le_sq_div_two (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have h1 : Real.cos x = 1 - 2 * Real.sin (x/2) ^ 2 := by
    have hcm := Real.cos_two_mul (x/2)
    have hsc := Real.sin_sq_add_cos_sq (x/2)
    have hx2 : 2 * (x/2) = x := by ring
    rw [hx2] at hcm
    nlinarith [hcm, hsc]
  have habs := Real.abs_sin_le_abs (x := x/2)
  have h2 : Real.sin (x/2) ^ 2 ≤ (x/2) ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg (Real.sin (x/2))) habs 2
    rwa [sq_abs, sq_abs] at hp
  nlinarith [h1, h2]

/-- Cosine is at most `1`, so `1 - cos x` is always nonnegative. -/
theorem one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]

/-- **The normalized floor `⌊n * s⌋₊ / n` converges to `s`.** -/
theorem tendsto_nat_floor_div (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * s⌋₊ : ℝ) / n) atTop (𝓝 s) := by
  have h1 : Tendsto (fun n : ℕ => s - (1 : ℝ) / n) atTop (𝓝 (s - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
    rw [le_div_iff₀ hn0]
    have h := Nat.lt_floor_add_one ((n : ℝ) * s)
    calc (s - 1 / (n : ℝ)) * (n : ℝ) = (n : ℝ) * s - 1 := by
          rw [sub_mul, one_div_mul_cancel hn0']; ring
      _ ≤ ⌊(n : ℝ) * s⌋₊ := by rw [sub_le_iff_le_add]; exact h.le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [div_le_iff₀ hn0]
    calc (⌊(n : ℝ) * s⌋₊ : ℝ) ≤ (n : ℝ) * s :=
          Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hs)
      _ = s * n := by ring

/-- **Squaring the step coefficient `Λⱼ` and summing over `j` counts, for each pair
`(i, l)`, the number `min (k i) (k l)` of steps below both cutoffs.** Its proof uses nothing
about the driving distribution. -/
theorem sum_sq_indicator {m : ℕ} (u : Fin m → ℝ) (k : Fin m → ℕ) (K : ℕ)
    (hK : ∀ i, k i ≤ K) :
    ∑ j ∈ Finset.range K, (∑ i : Fin m, if j < k i then u i else 0) ^ 2
      = ∑ i : Fin m, ∑ l : Fin m, u i * u l * (min (k i) (k l) : ℝ) := by
  simp only [pow_two]
  have step1 : ∑ j ∈ Finset.range K, (∑ i : Fin m, if j < k i then u i else 0)
        * (∑ l : Fin m, if j < k l then u l else 0)
      = ∑ j ∈ Finset.range K, ∑ i : Fin m, ∑ l : Fin m,
        (if j < k i then u i else 0) * (if j < k l then u l else 0) :=
    Finset.sum_congr rfl fun j _ => Fintype.sum_mul_sum _ _
  rw [step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hite : ∀ j : ℕ, (if j < k i then u i else 0) * (if j < k l then u l else 0)
      = if j < min (k i) (k l) then u i * u l else 0 := by
    intro j
    by_cases h : j < min (k i) (k l)
    · rw [if_pos h]
      rw [lt_min_iff] at h
      rw [if_pos h.1, if_pos h.2]
    · rw [if_neg h]
      rw [lt_min_iff, not_and] at h
      by_cases hi : j < k i
      · rw [if_pos hi, if_neg (h hi), mul_zero]
      · rw [if_neg hi, zero_mul]
  have hfilter : (Finset.range K).filter (fun j => j < min (k i) (k l))
      = Finset.range (min K (min (k i) (k l))) := by
    ext j
    simp
  calc ∑ j ∈ Finset.range K, (if j < k i then u i else 0) * (if j < k l then u l else 0)
      = ∑ j ∈ Finset.range K, if j < min (k i) (k l) then u i * u l else 0 :=
        Finset.sum_congr rfl fun j _ => hite j
    _ = ∑ j ∈ (Finset.range K).filter (fun j => j < min (k i) (k l)), u i * u l := by
        rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.range (min K (min (k i) (k l))), u i * u l := by rw [hfilter]
    _ = (Finset.range (min K (min (k i) (k l)))).card • (u i * u l) := Finset.sum_const _
    _ = (min (k i) (k l) : ℝ) * (u i * u l) := by
        rw [Finset.card_range, nsmul_eq_mul,
          min_eq_right (le_trans (min_le_left _ _) (hK i)), Nat.cast_min]
    _ = u i * u l * (min (k i) (k l) : ℝ) := by ring

/-- **The successive-increments swap**: `∑ᵢ w(i) · ∑_{j<k(i)} f(j) = ∑_{j<K} (∑ᵢ [j<k(i)]
w(i)) · f(j)`, for any weight `w`, cutoffs `k` bounded by `K`, and function `f`. General, no
model content. -/
theorem sum_range_swap_indicator {m : ℕ} (k : Fin m → ℕ) (K : ℕ) (hkK : ∀ i, k i ≤ K)
    (w : Fin m → ℝ) (f : ℕ → ℝ) :
    ∑ i, w i * ∑ j ∈ Finset.range (k i), f j
      = ∑ j ∈ Finset.range K, (∑ i, if j < k i then w i else 0) * f j := by
  have step1 : ∀ i : Fin m, w i * ∑ j ∈ Finset.range (k i), f j
      = ∑ j ∈ Finset.range K, (if j < k i then w i * f j else 0) := by
    intro i
    rw [Finset.mul_sum]
    calc ∑ j ∈ Finset.range (k i), w i * f j
        = ∑ j ∈ Finset.range (k i), (if j < k i then w i * f j else 0) :=
          Finset.sum_congr rfl fun j hj => by
            rw [Finset.mem_range] at hj; exact (if_pos hj).symm
      _ = ∑ j ∈ Finset.range K, (if j < k i then w i * f j else 0) :=
          Finset.sum_subset (Finset.range_mono (hkK i)) fun j _ hj => by
            rw [Finset.mem_range] at hj; exact if_neg hj
  calc ∑ i, w i * ∑ j ∈ Finset.range (k i), f j
      = ∑ i, ∑ j ∈ Finset.range K, (if j < k i then w i * f j else 0) :=
        Finset.sum_congr rfl fun i _ => step1 i
    _ = ∑ j ∈ Finset.range K, ∑ i, (if j < k i then w i * f j else 0) := Finset.sum_comm
    _ = ∑ j ∈ Finset.range K, (∑ i, if j < k i then w i else 0) * f j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring

end LatticeProb.Scaling.WalkCLT
