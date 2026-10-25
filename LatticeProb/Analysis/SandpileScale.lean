module

/-
Numerical scale bounds for the exploding-square estimate.

For `2 ≤ d`, `N0 : ℕ`, and `n ≥ 1`, the natural number `N = (2n+3)^d + N0` satisfies
`N ≤ (5^d + N0) n^d`. Consequently its real `d`-th root grows at most linearly in `n`, the
integer ceiling `L` of `A N^(1/d)` satisfies `L + 2 ≤ P n` for a constant `P`, and the scale
expression is bounded by `C n^d` (for `d ≥ 3`) or by `C n^2 log (n+1)` (for `d = 2`).
These are purely numerical inequalities with no radius, Green, wave, or source premise.
-/
public import Mathlib

@[expose] public section

namespace LatticeProb

/-- The cast of `Nat.pow (2 * n + 3) d + N0` is `(2 n + 3)^d + N0` in `ℝ`. -/
theorem sandpile_nat_cast_eq (d N0 n : ℕ) :
    ((Nat.pow (2 * n + 3) d + N0 : ℕ) : ℝ) = (2 * (n : ℝ) + 3) ^ d + (N0 : ℝ) := by
  simp [Nat.pow_eq]

/-- If `0 ≤ x ≤ D n^d`, then `x^(1/d) ≤ D^(1/d) n` for `d ≠ 0`. -/
theorem sandpile_rpow_inv_le_mul (x D n : ℝ) (d : ℕ) (hd : d ≠ 0) (hx : 0 ≤ x)
    (hD : 0 ≤ D) (hn : 0 ≤ n) (h : x ≤ D * n ^ d) :
    Real.rpow x (1 / (d : ℝ)) ≤ Real.rpow D (1 / (d : ℝ)) * n := by
  have hpow : 0 ≤ n ^ d := pow_nonneg hn d
  have hexp : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have h1 : x ^ (1 / (d : ℝ)) ≤ (D * n ^ d) ^ (1 / (d : ℝ)) := Real.rpow_le_rpow hx h hexp
  have h2 : (D * n ^ d) ^ (1 / (d : ℝ)) = D ^ (1 / (d : ℝ)) * n := by
    rw [Real.mul_rpow hD hpow, one_div, Real.pow_rpow_inv_natCast hn hd]
  exact h1.trans_eq h2

/-- Ceiling bound: if `0 ≤ x ≤ K n` and `1 ≤ n`, then `⌈x⌉₊ + 2 ≤ (K + 3) n`. -/
theorem sandpile_ceil_add_two_le (x K n : ℝ) (hx : 0 ≤ x) (hxK : x ≤ K * n) (hn : 1 ≤ n) :
    ((Nat.ceil x : ℕ) : ℝ) + 2 ≤ (K + 3) * n := by
  have h1 : ((Nat.ceil x : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have h2 : (K + 3) * n = K * n + 3 * n := by ring
  rw [h2]
  linarith

/-- The five-power bound `(2n+3)^d + N0 ≤ (5^d + N0) n^d` for `1 ≤ n`. -/
theorem sandpile_nat_le_five_pow (d N0 n : ℕ) (hn : 1 ≤ n) :
    ((Nat.pow (2 * n + 3) d + N0 : ℕ) : ℝ) ≤ ((5 : ℝ) ^ d + (N0 : ℝ)) * (n : ℝ) ^ d := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnd : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ hn'
  have h2n : 2 * (n : ℝ) + 3 ≤ 5 * (n : ℝ) := by linarith
  have hpow : (2 * (n : ℝ) + 3) ^ d ≤ (5 : ℝ) ^ d * (n : ℝ) ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) h2n d
  have hN0 : (N0 : ℝ) ≤ (N0 : ℝ) * (n : ℝ) ^ d :=
    le_mul_of_one_le_right (Nat.cast_nonneg N0) hnd
  have hsplit : ((5 : ℝ) ^ d + (N0 : ℝ)) * (n : ℝ) ^ d
      = (5 : ℝ) ^ d * (n : ℝ) ^ d + (N0 : ℝ) * (n : ℝ) ^ d := by
    ring
  rw [sandpile_nat_cast_eq d N0 n, hsplit]
  linarith

/-- Constants `D ≥ 1` and `P ≥ 3`, depending only on `d`, `N0`, and `A`, such that for every
`n ≥ 1`, `N ≤ D n^d` and `L + 2 ≤ P n`, where `N = (2n+3)^d + N0` and `L = ⌈A N^(1/d)⌉₊`. -/
theorem sandpile_scale_constants (d N0 : ℕ) (A : ℝ) (hd : 2 ≤ d) (hA : 0 < A) :
    ∃ D P : ℝ, 1 ≤ D ∧ 3 ≤ P ∧ ∀ n : ℕ, 1 ≤ n →
      ((Nat.pow (2 * n + 3) d + N0 : ℕ) : ℝ) ≤ D * (n : ℝ) ^ d ∧
        ((Nat.ceil (A * Real.rpow ((Nat.pow (2 * n + 3) d + N0 : ℕ) : ℝ) (1 / (d : ℝ))) : ℕ) : ℝ)
            + 2 ≤ P * (n : ℝ) := by
  have hd0 : d ≠ 0 := by omega
  have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hN0 : (0 : ℝ) ≤ (N0 : ℝ) := Nat.cast_nonneg N0
  have hD1 : (1 : ℝ) ≤ (5 : ℝ) ^ d + (N0 : ℝ) := by linarith
  have hD0 : (0 : ℝ) ≤ (5 : ℝ) ^ d + (N0 : ℝ) := by linarith
  have hK0 : 0 ≤ A * Real.rpow ((5 : ℝ) ^ d + (N0 : ℝ)) (1 / (d : ℝ)) :=
    mul_nonneg hA.le (Real.rpow_nonneg hD0 _)
  refine ⟨(5 : ℝ) ^ d + (N0 : ℝ), A * Real.rpow ((5 : ℝ) ^ d + (N0 : ℝ)) (1 / (d : ℝ)) + 3,
    hD1, by linarith, ?_⟩
  intro n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by linarith
  have hNle := sandpile_nat_le_five_pow d N0 n hn
  refine ⟨hNle, ?_⟩
  have hroot := sandpile_rpow_inv_le_mul ((Nat.pow (2 * n + 3) d + N0 : ℕ) : ℝ)
    ((5 : ℝ) ^ d + (N0 : ℝ)) (n : ℝ) d hd0 (Nat.cast_nonneg _) hD0 hn0 hNle
  have hx0 : 0 ≤ A * Real.rpow ((Nat.pow (2 * n + 3) d + N0 : ℕ) : ℝ) (1 / (d : ℝ)) :=
    mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hxK : A * Real.rpow ((Nat.pow (2 * n + 3) d + N0 : ℕ) : ℝ) (1 / (d : ℝ)) ≤
      (A * Real.rpow ((5 : ℝ) ^ d + (N0 : ℝ)) (1 / (d : ℝ))) * (n : ℝ) := by
    calc A * Real.rpow ((Nat.pow (2 * n + 3) d + N0 : ℕ) : ℝ) (1 / (d : ℝ))
        ≤ A * (Real.rpow ((5 : ℝ) ^ d + (N0 : ℝ)) (1 / (d : ℝ)) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hroot hA.le
      _ = (A * Real.rpow ((5 : ℝ) ^ d + (N0 : ℝ)) (1 / (d : ℝ))) * (n : ℝ) := by ring
  exact sandpile_ceil_add_two_le _ _ _ hx0 hxK hn'

/-- Root bound: with `N = (2n+3)^d + N0` and `d ≥ 2`, `n ≤ ((N + 2d - 2)^(1/d) - 3) / 2`. -/
theorem le_sandpile_scale_root (d n N0 : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    let N : ℕ := Nat.pow (2 * n + 3) d + N0
    (n : ℝ) ≤ (Real.rpow ((N : ℝ) + 2 * (d : ℝ) - 2) (1 / (d : ℝ)) - 3) / 2 := by
  intro N
  have hd0 : d ≠ 0 := by omega
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hNcast : (N : ℝ) = (2 * (n : ℝ) + 3) ^ d + (N0 : ℝ) := sandpile_nat_cast_eq d N0 n
  have hN0 : (0 : ℝ) ≤ (N0 : ℝ) := Nat.cast_nonneg N0
  have hbase : (2 * (n : ℝ) + 3) ^ d ≤ (N : ℝ) + 2 * (d : ℝ) - 2 := by linarith
  have hbase0 : (0 : ℝ) ≤ (2 * (n : ℝ) + 3) ^ d := by positivity
  have hexp : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have h1 := Real.rpow_le_rpow hbase0 hbase hexp
  have h2 : ((2 * (n : ℝ) + 3) ^ d) ^ (1 / (d : ℝ)) = 2 * (n : ℝ) + 3 := by
    rw [one_div]
    exact Real.pow_rpow_inv_natCast (by positivity) hd0
  have hroot : 2 * (n : ℝ) + 3 ≤ Real.rpow ((N : ℝ) + 2 * (d : ℝ) - 2) (1 / (d : ℝ)) := by
    rw [← h2]
    exact h1
  linarith

/-- Scale bound: there is `C > 0`, depending only on `d`, `N0`, `A`, `B`, `E`, such that for every
`n ≥ 1`, with `N = (2n+3)^d + N0` and `L = ⌈A N^(1/d)⌉₊`,
`N B (log (L+2) if d = 2) + (2d-2) E (L+1)^2 ≤ C n^d (log (n+1) if d = 2)`. -/
theorem exists_sandpile_scale_bound (d N0 : ℕ) (A B E : ℝ) (hd : 2 ≤ d)
    (hA : 0 < A) (hB : 0 < B) (hE : 0 < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      let N : ℕ := Nat.pow (2 * n + 3) d + N0
      let L : ℕ := Nat.ceil (A * Real.rpow (N : ℝ) (1 / (d : ℝ)))
      (N : ℝ) * B * (if d = 2 then Real.log ((L : ℝ) + 2) else 1)
        + (2 * (d : ℝ) - 2) * E * Real.rpow ((L : ℝ) + 1) 2
        ≤ C * Real.rpow (n : ℝ) (d : ℝ) * (if d = 2 then Real.log ((n : ℝ) + 1) else 1) := by
  obtain ⟨D, P, hD1, hP3, hest⟩ := sandpile_scale_constants d N0 A hd hA
  have hD0 : 0 < D := by linarith
  have hP0 : 0 < P := by linarith
  have hc2 : (0 : ℝ) ≤ 2 * (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  by_cases hd2 : d = 2
  · -- `d = 2`: the logarithmic rate
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2ne : Real.log 2 ≠ 0 := hlog2.ne'
    have hu : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.2 hlog2.le
    have hlogP : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
    have hPu : 0 ≤ Real.log P * (Real.log 2)⁻¹ := mul_nonneg hlogP hu
    have hdR : (d : ℝ) = 2 := by simp [hd2]
    have hCpos : 0 < D * B * (Real.log P * (Real.log 2)⁻¹ + 1)
        + (2 * 2 - 2) * E * P ^ 2 * (Real.log 2)⁻¹ := by
      have h1 : 0 < D * B * (Real.log P * (Real.log 2)⁻¹ + 1) :=
        mul_pos (mul_pos hD0 hB) (by linarith)
      have h2 : 0 ≤ (2 * 2 - 2) * E * P ^ 2 * (Real.log 2)⁻¹ :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hE.le) (sq_nonneg P)) hu
      linarith
    refine ⟨_, hCpos, ?_⟩
    intro n hn N L
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hN : (N : ℝ) ≤ D * (n : ℝ) ^ 2 := by
      calc (N : ℝ) ≤ D * (n : ℝ) ^ d := (hest n hn).1
        _ = D * (n : ℝ) ^ 2 := by rw [hd2]
    have hL : (L : ℝ) + 2 ≤ P * (n : ℝ) := (hest n hn).2
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    have hLsq : ((L : ℝ) + 1) ^ 2 ≤ P ^ 2 * (n : ℝ) ^ 2 := by
      have h1 : (L : ℝ) + 1 ≤ P * (n : ℝ) := by linarith
      calc ((L : ℝ) + 1) ^ 2 ≤ (P * (n : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
        _ = P ^ 2 * (n : ℝ) ^ 2 := by ring
    have hℓ2 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlogL : Real.log ((L : ℝ) + 2)
        ≤ (Real.log P * (Real.log 2)⁻¹ + 1) * Real.log ((n : ℝ) + 1) := by
      have h1 : Real.log ((L : ℝ) + 2) ≤ Real.log (P * (n : ℝ)) :=
        Real.log_le_log (by linarith) hL
      have h2 : Real.log (P * (n : ℝ)) = Real.log P + Real.log (n : ℝ) :=
        Real.log_mul hP0.ne' hn0.ne'
      have h3 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log hn0 (by linarith)
      have e : Real.log P = (Real.log P * (Real.log 2)⁻¹) * Real.log 2 := by
        rw [mul_assoc, inv_mul_cancel₀ hlog2ne, mul_one]
      have h4 : Real.log P ≤ (Real.log P * (Real.log 2)⁻¹) * Real.log ((n : ℝ) + 1) := by
        calc Real.log P = (Real.log P * (Real.log 2)⁻¹) * Real.log 2 := e
          _ ≤ (Real.log P * (Real.log 2)⁻¹) * Real.log ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hℓ2 hPu
      have e2 : (Real.log P * (Real.log 2)⁻¹ + 1) * Real.log ((n : ℝ) + 1)
          = (Real.log P * (Real.log 2)⁻¹) * Real.log ((n : ℝ) + 1) + Real.log ((n : ℝ) + 1) := by
        ring
      linarith
    have hDnB : 0 ≤ D * (n : ℝ) ^ 2 * B := mul_nonneg (mul_nonneg hD0.le (sq_nonneg _)) hB.le
    have hlog0 : 0 ≤ Real.log ((L : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hT1a : (N : ℝ) * B * Real.log ((L : ℝ) + 2)
        ≤ D * (n : ℝ) ^ 2 * B * Real.log ((L : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN hB.le) hlog0
    have hT1b : D * (n : ℝ) ^ 2 * B * Real.log ((L : ℝ) + 2)
        ≤ D * (n : ℝ) ^ 2 * B * ((Real.log P * (Real.log 2)⁻¹ + 1) * Real.log ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hlogL hDnB
    have hT2 : (2 * 2 - 2) * E * ((L : ℝ) + 1) ^ 2
        ≤ (2 * 2 - 2) * E * (P ^ 2 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hLsq (mul_nonneg (by norm_num) hE.le)
    have hT3 : (2 * 2 - 2) * E * (P ^ 2 * (n : ℝ) ^ 2)
        ≤ (2 * 2 - 2) * E * P ^ 2 * (Real.log 2)⁻¹ * ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) := by
      have hq : 1 ≤ (Real.log 2)⁻¹ * Real.log ((n : ℝ) + 1) := by
        have h := mul_le_mul_of_nonneg_left hℓ2 hu
        rwa [inv_mul_cancel₀ hlog2ne] at h
      have hK : 0 ≤ (2 * 2 - 2) * E * (P ^ 2 * (n : ℝ) ^ 2) :=
        mul_nonneg (mul_nonneg (by norm_num) hE.le) (mul_nonneg (sq_nonneg P) (sq_nonneg _))
      have h := mul_le_mul_of_nonneg_left hq hK
      calc (2 * 2 - 2) * E * (P ^ 2 * (n : ℝ) ^ 2)
          = (2 * 2 - 2) * E * (P ^ 2 * (n : ℝ) ^ 2) * 1 := by ring
        _ ≤ (2 * 2 - 2) * E * (P ^ 2 * (n : ℝ) ^ 2) * ((Real.log 2)⁻¹ * Real.log ((n : ℝ) + 1)) :=
          h
        _ = (2 * 2 - 2) * E * P ^ 2 * (Real.log 2)⁻¹ * ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) := by
          ring
    have hC : (D * B * (Real.log P * (Real.log 2)⁻¹ + 1)
          + (2 * 2 - 2) * E * P ^ 2 * (Real.log 2)⁻¹) * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)
        = D * (n : ℝ) ^ 2 * B * ((Real.log P * (Real.log 2)⁻¹ + 1) * Real.log ((n : ℝ) + 1))
          + (2 * 2 - 2) * E * P ^ 2 * (Real.log 2)⁻¹ * ((n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1)) := by
      ring
    simp only [if_pos hd2, hdR, Real.rpow_eq_pow, Real.rpow_two]
    linarith [hT1a, hT1b, hT2, hT3, hC]
  · -- `d ≥ 3`: the polynomial rate
    have hCpos : 0 < D * B + (2 * (d : ℝ) - 2) * E * P ^ 2 := by
      have h1 : 0 < D * B := mul_pos hD0 hB
      have h2 : 0 ≤ (2 * (d : ℝ) - 2) * E * P ^ 2 :=
        mul_nonneg (mul_nonneg hc2 hE.le) (sq_nonneg P)
      linarith
    refine ⟨_, hCpos, ?_⟩
    intro n hn N L
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hN : (N : ℝ) ≤ D * (n : ℝ) ^ d := (hest n hn).1
    have hL : (L : ℝ) + 2 ≤ P * (n : ℝ) := (hest n hn).2
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
    have hLsq : ((L : ℝ) + 1) ^ 2 ≤ P ^ 2 * (n : ℝ) ^ d := by
      have h1 : (L : ℝ) + 1 ≤ P * (n : ℝ) := by linarith
      have h2 : ((L : ℝ) + 1) ^ 2 ≤ (P * (n : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      have h3 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ d := pow_le_pow_right₀ hn' hd
      calc ((L : ℝ) + 1) ^ 2 ≤ (P * (n : ℝ)) ^ 2 := h2
        _ = P ^ 2 * (n : ℝ) ^ 2 := by ring
        _ ≤ P ^ 2 * (n : ℝ) ^ d := mul_le_mul_of_nonneg_left h3 (sq_nonneg P)
    have hT1 : (N : ℝ) * B ≤ D * (n : ℝ) ^ d * B := mul_le_mul_of_nonneg_right hN hB.le
    have hT2 : (2 * (d : ℝ) - 2) * E * ((L : ℝ) + 1) ^ 2
        ≤ (2 * (d : ℝ) - 2) * E * (P ^ 2 * (n : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_left hLsq (mul_nonneg hc2 hE.le)
    have hC : (D * B + (2 * (d : ℝ) - 2) * E * P ^ 2) * (n : ℝ) ^ d
        = D * (n : ℝ) ^ d * B + (2 * (d : ℝ) - 2) * E * (P ^ 2 * (n : ℝ) ^ d) := by
      ring
    simp only [if_neg hd2, mul_one, Real.rpow_eq_pow, Real.rpow_natCast, Real.rpow_two]
    linarith [hT1, hT2, hC]

end LatticeProb
