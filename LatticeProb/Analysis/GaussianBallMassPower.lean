import Mathlib

/-!
# Gaussian kernels against measures with power-law ball masses

Let `μ` be a measure on a pseudometric space with `μ (ball z r) ≤ A r^β` for every `r > 0`, where
`0 < β ≤ 1`. Then the Gaussian weight `exp (-d(x, z)² / (2 s))` integrates against `μ` to at most
`(1024 / 7) A s^{β/2}` (`lintegral_exp_neg_dist_sq_le_of_measure_ball_le`).

The proof splits space into the dyadic shells `2^{j-1} √s ≤ d(x, z) < 2^j √s`: on the `j`-th shell
the weight is at most `128 / 16^j` (from `exp y ≥ y² / 2`), the shell has mass at most
`A 2^j s^{β/2}`, and the resulting series is geometric with ratio `1/8`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

/-- On the shell `d ≥ 2^i √s` the Gaussian weight `exp (-d² / (2 s))` is at most `128 / 16^{i+1}`. -/
theorem exp_neg_sq_div_le_of_two_pow_mul_sqrt_le {d s : ℝ} (hs : 0 < s) (i : ℕ)
    (hd : (2 : ℝ) ^ i * Real.sqrt s ≤ d) :
    Real.exp (-(d ^ 2) / (2 * s)) ≤ 128 / 16 ^ (i + 1) := by
  have h0 : 0 ≤ (2 : ℝ) ^ i * Real.sqrt s := by positivity
  have hsq : (4 : ℝ) ^ i * s ≤ d ^ 2 := by
    have h := pow_le_pow_left₀ h0 hd 2
    have h4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, Real.sq_sqrt hs.le, h4] at h
    exact h
  set y : ℝ := (4 : ℝ) ^ i / 2 with hy
  have hypos : 0 < y := by positivity
  have hyd : y ≤ d ^ 2 / (2 * s) := by
    rw [le_div_iff₀ (by positivity)]
    have : y * (2 * s) = 4 ^ i * s := by rw [hy]; ring
    linarith
  have hq := Real.quadratic_le_exp_of_nonneg hypos.le
  have hy2 : 0 < y ^ 2 / 2 := by positivity
  calc Real.exp (-(d ^ 2) / (2 * s)) ≤ Real.exp (-y) := by
        apply Real.exp_le_exp.2; rw [neg_div]; linarith
    _ = (Real.exp y)⁻¹ := Real.exp_neg y
    _ ≤ (y ^ 2 / 2)⁻¹ := inv_anti₀ hy2 (by linarith)
    _ = 128 / 16 ^ (i + 1) := by
        have h16 : (16 : ℝ) ^ i = ((4 : ℝ) ^ i) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [hy, pow_succ (16 : ℝ) i, h16]
        field_simp
        ring

/-- Pointwise domination of the Gaussian weight by a series of indicators of dyadic balls. -/
theorem ofReal_exp_neg_dist_sq_le_tsum_indicator {α : Type*} [PseudoMetricSpace α] (z x : α)
    {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s))) ≤
      ∑' j : ℕ, (ball z ((2 : ℝ) ^ j * Real.sqrt s)).indicator
        (fun _ => ENNReal.ofReal (128 / 16 ^ j)) x := by
  classical
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hex : ∃ j : ℕ, dist x z < (2 : ℝ) ^ j * Real.sqrt s := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (dist x z / Real.sqrt s) (by norm_num : (1 : ℝ) < 2)
    exact ⟨j, by rwa [div_lt_iff₀ hss] at hj⟩
  obtain ⟨j, hj, hmin⟩ : ∃ j : ℕ, dist x z < (2 : ℝ) ^ j * Real.sqrt s ∧
      ∀ m < j, ¬ dist x z < (2 : ℝ) ^ m * Real.sqrt s :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine le_trans ?_ (ENNReal.le_tsum j)
  rw [indicator_of_mem (mem_ball.2 hj)]
  refine ENNReal.ofReal_le_ofReal ?_
  cases j with
  | zero =>
    have hle : -(dist x z ^ 2) / (2 * s) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)
    have := Real.exp_le_one_iff.2 hle
    norm_num
    linarith
  | succ i =>
    exact exp_neg_sq_div_le_of_two_pow_mul_sqrt_le hs i
      (not_lt.1 (hmin i (Nat.lt_succ_self i)))

/-- **Gaussian weights against a measure with power-law ball masses.** If
`μ (ball z r) ≤ A r^β` for every `r > 0`, with `0 < β ≤ 1` and `A ≥ 0`, then
`∫ exp (-d(x, z)² / (2 s)) dμ(x) ≤ (1024 / 7) A s^{β/2}` for every `s > 0`. -/
theorem lintegral_exp_neg_dist_sq_le_of_measure_ball_le {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} {z : α} {A β s : ℝ}
    (hβ1 : β ≤ 1) (hA : 0 ≤ A) (hs : 0 < s)
    (hball : ∀ r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (A * r ^ β)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s))) ∂μ ≤
      ENNReal.ofReal (1024 / 7 * A * s ^ (β / 2)) := by
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hS : 0 ≤ s ^ (β / 2) := Real.rpow_nonneg hs.le _
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-(dist x z ^ 2) / (2 * s))) ∂μ
      ≤ ∫⁻ x, ∑' j : ℕ, (ball z ((2 : ℝ) ^ j * Real.sqrt s)).indicator
          (fun _ => ENNReal.ofReal (128 / 16 ^ j)) x ∂μ :=
        lintegral_mono fun x => ofReal_exp_neg_dist_sq_le_tsum_indicator z x hs
    _ = ∑' j : ℕ, ENNReal.ofReal (128 / 16 ^ j) * μ (ball z ((2 : ℝ) ^ j * Real.sqrt s)) := by
        rw [lintegral_tsum fun j => (measurable_const.indicator measurableSet_ball).aemeasurable]
        congr 1
        ext j
        rw [lintegral_indicator_const measurableSet_ball]
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (128 * A * s ^ (β / 2) * (1 / 8) ^ j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        have hr : 0 < (2 : ℝ) ^ j * Real.sqrt s := by positivity
        calc ENNReal.ofReal (128 / 16 ^ j) * μ (ball z ((2 : ℝ) ^ j * Real.sqrt s))
            ≤ ENNReal.ofReal (128 / 16 ^ j) *
                ENNReal.ofReal (A * ((2 : ℝ) ^ j * Real.sqrt s) ^ β) :=
              mul_le_mul' le_rfl (hball _ hr)
          _ = ENNReal.ofReal (128 / 16 ^ j * (A * ((2 : ℝ) ^ j * Real.sqrt s) ^ β)) :=
              (ENNReal.ofReal_mul (by positivity)).symm
          _ ≤ ENNReal.ofReal (128 * A * s ^ (β / 2) * (1 / 8) ^ j) := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hsb : (1 / 2 : ℝ) * β = β / 2 := by ring
              rw [Real.mul_rpow (by positivity) hss.le, Real.sqrt_eq_rpow,
                ← Real.rpow_mul hs.le, hsb]
              have h2 : ((2 : ℝ) ^ j) ^ β ≤ (2 : ℝ) ^ j := by
                calc ((2 : ℝ) ^ j) ^ β ≤ ((2 : ℝ) ^ j) ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hβ1
                  _ = (2 : ℝ) ^ j := Real.rpow_one _
              have h16 : (2 : ℝ) ^ j / 16 ^ j = (1 / 8) ^ j := by
                rw [← div_pow]; norm_num
              calc 128 / 16 ^ j * (A * (((2 : ℝ) ^ j) ^ β * s ^ (β / 2)))
                  ≤ 128 / 16 ^ j * (A * ((2 : ℝ) ^ j * s ^ (β / 2))) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hS) hA)
                      (by positivity)
                _ = 128 * A * s ^ (β / 2) * (1 / 8) ^ j := by rw [← h16]; ring
    _ = ENNReal.ofReal (1024 / 7 * A * s ^ (β / 2)) := by
        have hsum : Summable fun j : ℕ => 128 * A * s ^ (β / 2) * (1 / 8 : ℝ) ^ j :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hS) (by positivity)) hsum,
          tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        congr 1
        ring

end LatticeProb
