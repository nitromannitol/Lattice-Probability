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
import LatticeProb.Walk.CentralBinom

open Filter Finset Real MeasureTheory
open scoped Topology

noncomputable section

namespace LatticeProb.BinomialLCLT

/-- The probability that a sum of `m` independent signs equals `j`. -/
def binomPMF (m : ℕ) (j : ℤ) : ℝ := (m.choose ((m + j) / 2).toNat : ℝ) / 2 ^ m

/-- The standard normal density. -/
def gaussianDensity (x : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- The exponent of the binomial coefficient: `g t = (1+t)/2 log(1+t) + (1-t)/2 log(1-t)`. -/
def gfun (t : ℝ) : ℝ := (1 + t) / 2 * Real.log (1 + t) + (1 - t) / 2 * Real.log (1 - t)


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


/-- **Stirling's sequence is at most `√π e^{1/(12n)}`.**  This is Robbins' bound
`log (stirlingSeq n) - log (stirlingSeq (n+1)) ≤ 1/(12 n (n+1))` summed from `n` to infinity. -/
theorem stirlingSeq_le_sqrt_pi_mul_exp (n : ℕ) (hn : 1 ≤ n) :
    Stirling.stirlingSeq n ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * n)) := by
  have hn0 : n ≠ 0 := by omega
  have htel : ∀ k : ℕ, Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + k))
      = ∑ j ∈ Finset.range k, (Real.log (Stirling.stirlingSeq (n + j)) - Real.log (Stirling.stirlingSeq (n + j + 1))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring
  have hbound : ∀ k : ℕ, Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + k))
      ≤ ∑ j ∈ Finset.range k, (1 / (12 * ((n + j : ℕ) : ℝ) * (((n + j : ℕ) : ℝ) + 1))) := by
    intro k
    rw [htel k]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := Stirling.log_stirlingSeq_sdiff_le (n + j)
    push_cast at h ⊢
    exact h
  have hsum : ∀ k : ℕ, ∑ j ∈ Finset.range k, (1 / (12 * ((n + j : ℕ) : ℝ) * (((n + j : ℕ) : ℝ) + 1))) ≤ 1 / (12 * n) := by
    intro k
    have htel2 : ∑ j ∈ Finset.range k, (1 / (((n + j : ℕ) : ℝ)) - 1 / (((n + j : ℕ) : ℝ) + 1)) = 1 / n - 1 / ((n + k : ℕ) : ℝ) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    have hterm : ∀ j ∈ Finset.range k, (1 / (12 * ((n + j : ℕ) : ℝ) * (((n + j : ℕ) : ℝ) + 1)))
        ≤ (1 / (((n + j : ℕ) : ℝ)) - 1 / (((n + j : ℕ) : ℝ) + 1)) / 12 := by
      intro j _
      have h1 : ((n + j : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : ((n + j : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      have heq : (1 / (12 * ((n + j : ℕ) : ℝ) * (((n + j : ℕ) : ℝ) + 1)))
          = (1 / (((n + j : ℕ) : ℝ)) - 1 / (((n + j : ℕ) : ℝ) + 1)) / 12 := by
        field_simp
        ring
      rw [heq]
    calc ∑ j ∈ Finset.range k, (1 / (12 * ((n + j : ℕ) : ℝ) * (((n + j : ℕ) : ℝ) + 1)))
        ≤ ∑ j ∈ Finset.range k, (1 / (((n + j : ℕ) : ℝ)) - 1 / (((n + j : ℕ) : ℝ) + 1)) / 12 := Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range k, (1 / (((n + j : ℕ) : ℝ)) - 1 / (((n + j : ℕ) : ℝ) + 1))) / 12 := by rw [Finset.sum_div]
      _ = (1 / n - 1 / ((n + k : ℕ) : ℝ)) / 12 := by rw [htel2]
      _ ≤ (1 / n) / 12 := by
        have : (0:ℝ) < 1 / ((n + k : ℕ) : ℝ) := by positivity
        linarith
      _ = 1 / (12 * n) := by ring
  have hlog : Real.log (Stirling.stirlingSeq n) ≤ Real.log (Real.sqrt Real.pi) + 1 / (12 * n) := by
    have hlim : Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq (k + n))) atTop (𝓝 (Real.log (Real.sqrt Real.pi))) :=
      (Real.continuousAt_log (by positivity)).tendsto.comp
        (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat n))
    have h2 : ∀ k, Real.log (Stirling.stirlingSeq n) - 1 / (12 * n) ≤ Real.log (Stirling.stirlingSeq (k + n)) := by
      intro k
      rw [Nat.add_comm k n]
      linarith [hbound k, hsum k]
    have := ge_of_tendsto hlim (Eventually.of_forall h2)
    linarith
  have hpos : 0 < Stirling.stirlingSeq n := by
    have := Stirling.stirlingSeq'_pos (n - 1)
    rwa [show n - 1 + 1 = n from by omega] at this
  rw [← Real.exp_log (by positivity : (0:ℝ) < Real.sqrt Real.pi), ← Real.exp_add,
    ← Real.log_le_iff_le_exp hpos]
  linarith

/-- **Stirling's sequence is at least `√π`.** -/
theorem sqrt_pi_le_stirlingSeq' (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt Real.pi ≤ Stirling.stirlingSeq n :=
  Stirling.sqrt_pi_le_stirlingSeq (by omega)

/-- The Stirling ratio of the central binomial coefficient is at most `exp (1/(24m))`. -/
theorem stirling_ratio_le (m : ℕ) (hm : 1 ≤ m) :
    Stirling.stirlingSeq (2 * m) * Real.sqrt Real.pi / Stirling.stirlingSeq m ^ 2
      ≤ Real.exp (1 / (24 * (m : ℝ))) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hS2m := stirlingSeq_le_sqrt_pi_mul_exp (2 * m) (by omega)
  have hSml := sqrt_pi_le_stirlingSeq' m hm
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hSmpos : 0 < Stirling.stirlingSeq m := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) hSml
  rw [div_le_iff₀ (by positivity : (0:ℝ) < Stirling.stirlingSeq m ^ 2)]
  have h5 : Real.exp (1 / (12 * (2 * (m : ℝ)))) ≤ Real.exp (1 / (24 * (m : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : Real.sqrt Real.pi ^ 2 ≤ Stirling.stirlingSeq m ^ 2 := by
    nlinarith [hSml, Real.sqrt_pos.mpr Real.pi_pos]
  have h6 : Stirling.stirlingSeq (2 * m) * Real.sqrt Real.pi
      ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * (2 * (m : ℝ)))) * Real.sqrt Real.pi := by
    have h := mul_le_mul_of_nonneg_right hS2m (Real.sqrt_nonneg Real.pi)
    push_cast at h ⊢
    linarith [h]
  have h7 : Real.sqrt Real.pi * Real.exp (1 / (12 * (2 * (m : ℝ)))) * Real.sqrt Real.pi
      ≤ Real.exp (1 / (24 * (m : ℝ))) * Stirling.stirlingSeq m ^ 2 := by
    have h9 : Real.pi ≤ Real.exp (1 / (24 * (m : ℝ))) * Real.pi := by
      nlinarith [Real.exp_pos (1 / (24 * (m : ℝ))), Real.one_le_exp (by positivity : (0:ℝ) ≤ 1 / (24 * (m : ℝ)))]
    have h10 : Real.sqrt Real.pi * Real.exp (1 / (12 * (2 * (m : ℝ)))) * Real.sqrt Real.pi
        ≤ Real.exp (1 / (24 * (m : ℝ))) * Real.pi := by
      nlinarith [h5, hsp, Real.exp_pos (1 / (12 * (2 * (m : ℝ)))), Real.sqrt_pos.mpr Real.pi_pos]
    nlinarith [h2, h10, h9, Real.exp_pos (1 / (24 * (m : ℝ)))]
  linarith [h6, h7]

/-- The Stirling ratio of the central binomial coefficient is at least `exp (-(1/(6m)))`. -/
theorem stirling_ratio_ge (m : ℕ) (hm : 1 ≤ m) :
    Real.exp (-(1 / (6 * (m : ℝ))))
      ≤ Stirling.stirlingSeq (2 * m) * Real.sqrt Real.pi / Stirling.stirlingSeq m ^ 2 := by
  have hS2ml := sqrt_pi_le_stirlingSeq' (2 * m) (by omega)
  have hSm := stirlingSeq_le_sqrt_pi_mul_exp m hm
  have hSml := sqrt_pi_le_stirlingSeq' m hm
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hSmpos : 0 < Stirling.stirlingSeq m := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) hSml
  rw [le_div_iff₀ (by positivity : (0:ℝ) < Stirling.stirlingSeq m ^ 2)]
  have h2 : Stirling.stirlingSeq m ^ 2 ≤ (Real.sqrt Real.pi * Real.exp (1 / (12 * (m : ℝ)))) ^ 2 := by
    nlinarith [hSm, Real.sqrt_pos.mpr Real.pi_pos, Real.exp_pos (1/(12*(m:ℝ))), hSml]
  have h5 : Real.exp (-(1 / (6 * (m : ℝ)))) * (Real.sqrt Real.pi * Real.exp (1 / (12 * (m : ℝ)))) ^ 2 ≤ Real.pi := by
    have he : Real.exp (-(1 / (6 * (m : ℝ)))) * Real.exp (1 / (12 * (m : ℝ))) * Real.exp (1 / (12 * (m : ℝ))) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      have : -(1 / (6 * (m : ℝ))) + 1 / (12 * (m : ℝ)) + 1 / (12 * (m : ℝ)) = 0 := by ring
      rw [this, Real.exp_zero]
    nlinarith [hsp, he, Real.exp_pos (1/(12*(m:ℝ))), Real.exp_pos (-(1/(6*(m:ℝ))))]
  have h6 : Real.sqrt Real.pi * Stirling.stirlingSeq (2 * m) ≥ Real.pi := by
    nlinarith [hS2ml, Real.sqrt_pos.mpr Real.pi_pos, hsp]
  have h7 : Real.exp (-(1 / (6 * (m : ℝ)))) * Stirling.stirlingSeq m ^ 2
      ≤ Real.exp (-(1 / (6 * (m : ℝ)))) * (Real.sqrt Real.pi * Real.exp (1 / (12 * (m : ℝ)))) ^ 2 := by
    nlinarith [h2, Real.exp_pos (-(1/(6*(m:ℝ))))]
  linarith [h5, h6, h7]

/-- `|exp x - 1| ≤ 2|x|` for `|x| ≤ 1`. -/
theorem abs_exp_sub_one_le_two_mul (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x - 1| ≤ 2 * |x| :=
  Real.abs_exp_sub_one_le hx

/-- The exponent identity behind the Stirling form of the binomial coefficient. -/
theorem gfun_mul_eq (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((a : ℝ) + b) * gfun (((a : ℝ) - b) / ((a : ℝ) + b))
      = (a : ℝ) * Real.log (2 * (a : ℝ) / ((a : ℝ) + b))
        + (b : ℝ) * Real.log (2 * (b : ℝ) / ((a : ℝ) + b))  := by
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hs : (0 : ℝ) < (a : ℝ) + b := by linarith
  have h1 : 1 + ((a : ℝ) - b) / ((a : ℝ) + b) = 2 * (a : ℝ) / ((a : ℝ) + b) := by
    field_simp; ring
  have h2 : 1 - ((a : ℝ) - b) / ((a : ℝ) + b) = 2 * (b : ℝ) / ((a : ℝ) + b) := by
    field_simp; ring
  rw [gfun, h1, h2]
  have e1 : ((a : ℝ) + b) * ((1 + ((a : ℝ) - b) / ((a : ℝ) + b)) / 2) = (a : ℝ) := by
    field_simp; ring
  have e2 : ((a : ℝ) + b) * ((1 - ((a : ℝ) - b) / ((a : ℝ) + b)) / 2) = (b : ℝ) := by
    field_simp; ring
  rw [mul_add]
  congr 1 <;> field_simp

theorem binomPMF_eq_factorial (m : ℕ) (j : ℤ) (hj : j ≡ (m : ℤ) [ZMOD 2]) (hj1 : |j| ≤ (m : ℝ)) :
    binomPMF m j
      = (m.factorial : ℝ)
        / ((((m : ℤ) + j) / 2).toNat.factorial * (((m : ℤ) - j) / 2).toNat.factorial * 2 ^ m : ℝ) := by
  have hb := abs_le.mp (by exact_mod_cast hj1 : |j| ≤ (m : ℤ))
  have hdvd2 : (2 : ℤ) ∣ ((m : ℤ) - j) := Int.ModEq.dvd hj
  have hdvd : (2 : ℤ) ∣ ((m : ℤ) + j) := by omega
  have hk : (((m : ℤ) + j) / 2).toNat ≤ m := by omega
  rw [binomPMF, Nat.cast_choose (K := ℝ) hk]
  rw [show (m - (((m : ℤ) + j) / 2).toNat) = (((m : ℤ) - j) / 2).toNat from by omega]
  rw [Nat.cast_factorial, Nat.cast_factorial, Nat.cast_factorial]
  ring

theorem expGfun (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.exp (-(((a : ℝ) + b) * gfun (((a : ℝ) - b) / ((a : ℝ) + b))))
      = ((a : ℝ) + b) ^ (a + b) / (2 ^ (a + b) * (a : ℝ) ^ a * (b : ℝ) ^ b) := by
  have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hab : (0:ℝ) < (a:ℝ) + b := by linarith
  have hgm := gfun_mul_eq a b ha hb
  rw [show -(((a:ℝ) + b) * gfun (((a:ℝ) - b) / ((a:ℝ) + b)))
      = -((a:ℝ) * Real.log (2 * (a:ℝ) / ((a:ℝ) + b))
          + (b:ℝ) * Real.log (2 * (b:ℝ) / ((a:ℝ) + b))) from by rw [← hgm]]
  rw [neg_add, Real.exp_add]
  rw [show Real.exp (-((a:ℝ) * Real.log (2 * (a:ℝ) / ((a:ℝ) + b))))
      = (((a:ℝ) + b) / (2 * (a:ℝ))) ^ a from by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by positivity), ← inv_pow, inv_div]]
  rw [show Real.exp (-((b:ℝ) * Real.log (2 * (b:ℝ) / ((a:ℝ) + b))))
      = (((a:ℝ) + b) / (2 * (b:ℝ))) ^ b from by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by positivity), ← inv_pow, inv_div]]
  rw [div_pow, div_pow, div_mul_div_comm, ← pow_add, mul_pow, mul_pow]
  field_simp
  ring

theorem sqrt_ratio_id (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Real.sqrt (A + B) * Real.sqrt (2 * (A + B)) / (Real.sqrt (2 * A) * Real.sqrt (2 * B))
      = Real.sqrt 2 / Real.sqrt (1 - ((A - B) / (A + B)) ^ 2) := by
  have hAB : 0 < A + B := by linarith
  have h1 : 1 - ((A - B) / (A + B)) ^ 2 = 4 * A * B / (A + B) ^ 2 := by
    field_simp
    ring
  have hs4 : Real.sqrt (4:ℝ) = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have h4AB : Real.sqrt (4 * A * B) = 2 * Real.sqrt A * Real.sqrt B := by
    rw [show (4:ℝ) * A * B = 4 * (A * B) from by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) (A * B),
      Real.sqrt_mul hA.le B, hs4]
    ring
  have hL2 : Real.sqrt (A + B) * Real.sqrt (2 * (A + B)) = Real.sqrt 2 * (A + B) := by
    rw [← Real.sqrt_mul hAB.le (2 * (A + B)), show (A + B) * (2 * (A + B)) = 2 * (A + B) ^ 2 from by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) ((A + B) ^ 2), Real.sqrt_sq hAB.le]
  rw [h1, Real.sqrt_div (by positivity) ((A + B) ^ 2), h4AB, Real.sqrt_sq hAB.le, hL2,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) A, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) B]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem stirling_ratio_identity (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.sqrt ((a : ℝ) + b) *
        (Stirling.stirlingSeq (a + b) *
            (Real.sqrt (2 * ((a : ℝ) + b)) * (((a : ℝ) + b) / Real.exp 1) ^ (a + b)) /
          (Stirling.stirlingSeq a * (Real.sqrt (2 * (a : ℝ)) * ((a : ℝ) / Real.exp 1) ^ a) *
              (Stirling.stirlingSeq b * (Real.sqrt (2 * (b : ℝ)) * ((b : ℝ) / Real.exp 1) ^ b)) *
            2 ^ (a + b)))
      = Stirling.stirlingSeq (a + b) / (Stirling.stirlingSeq a * Stirling.stirlingSeq b) *
          (Real.sqrt 2 / Real.sqrt (1 - (((a : ℝ) - b) / ((a : ℝ) + b)) ^ 2)) *
        Real.exp (-(((a : ℝ) + b) * gfun (((a : ℝ) - b) / ((a : ℝ) + b)))) := by
  have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hab : (0:ℝ) < (a:ℝ) + b := by linarith
  have hE := expGfun a b ha hb
  have hN := sqrt_ratio_id (a:ℝ) (b:ℝ) ha0 hb0
  rw [hE, ← hN]
  field_simp
  rw [div_pow, div_pow, div_pow]
  rw [show (rexp 1) ^ (a + b) = (rexp 1) ^ a * (rexp 1) ^ b from by rw [← pow_add]]
  field_simp

theorem sqrt_mul_binomPMF_eq (m : ℕ) (hm : 1 ≤ m) (j : ℤ)
    (hj : j ≡ (m : ℤ) [ZMOD 2]) (hj1 : |j| ≤ (m : ℝ) - 2) :
    Real.sqrt m * binomPMF m j
      = Stirling.stirlingSeq m
          / (Stirling.stirlingSeq (((m : ℤ) + j) / 2).toNat
              * Stirling.stirlingSeq (((m : ℤ) - j) / 2).toNat)
        * (Real.sqrt 2 / Real.sqrt (1 - ((j : ℝ) / (m : ℝ)) ^ 2))
        * Real.exp (-(m : ℝ) * gfun ((j : ℝ) / (m : ℝ))) := by
  set a : ℕ := (((m : ℤ) + j) / 2).toNat with ha
  set b : ℕ := (((m : ℤ) - j) / 2).toNat with hb
  have hbnd : -((m : ℤ) - 2) ≤ j ∧ j ≤ (m : ℤ) - 2 := abs_le.mp (by exact_mod_cast hj1 : |j| ≤ (m : ℤ) - 2)
  have hja : ((a : ℤ)) = ((m : ℤ) + j) / 2 := by
    rw [ha]; exact Int.toNat_of_nonneg (by omega)
  have hjb : ((b : ℤ)) = ((m : ℤ) - j) / 2 := by
    rw [hb]; exact Int.toNat_of_nonneg (by omega)
  have hdvd : (2 : ℤ) ∣ ((m : ℤ) + j) := by
    have h := Int.ModEq.dvd hj
    omega
  have hsum : a + b = m := by
    have h : ((a : ℤ)) + ((b : ℤ)) = (m : ℤ) := by
      rw [hja, hjb]
      omega
    exact_mod_cast h
  have hdiff : (a : ℝ) - (b : ℝ) = (j : ℝ) := by
    have h1 : ((a : ℤ)) - ((b : ℤ)) = j := by rw [hja, hjb]; omega
    exact_mod_cast h1
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hmR : (m : ℝ) = (a : ℝ) + (b : ℝ) := by
    have h : ((a + b : ℕ) : ℝ) = (m : ℝ) := by rw [hsum]
    push_cast at h ⊢; linarith
  rw [binomPMF_eq_factorial m j hj (by linarith)]
  rw [show (((m : ℤ) + j) / 2).toNat = a from rfl, show (((m : ℤ) - j) / 2).toNat = b from rfl]
  rw [show (m.factorial : ℝ)
      = Stirling.stirlingSeq m * Real.sqrt (2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m from by
    rw [Stirling.stirlingSeq]; field_simp]
  rw [show (a.factorial : ℝ)
      = Stirling.stirlingSeq a * Real.sqrt (2 * (a : ℝ)) * ((a : ℝ) / Real.exp 1) ^ a from by
    rw [Stirling.stirlingSeq]; field_simp]
  rw [show (b.factorial : ℝ)
      = Stirling.stirlingSeq b * Real.sqrt (2 * (b : ℝ)) * ((b : ℝ) / Real.exp 1) ^ b from by
    rw [Stirling.stirlingSeq]; field_simp]
  rw [← hsum]
  push_cast
  have key := stirling_ratio_identity a b ha1 hb1
  rw [show Real.sqrt (↑a + ↑b) * (Stirling.stirlingSeq (a + b) * √(2 * (↑a + ↑b)) * ((↑a + ↑b) / rexp 1) ^ (a + b)
        / (Stirling.stirlingSeq a * √(2 * ↑a) * (↑a / rexp 1) ^ a
            * (Stirling.stirlingSeq b * √(2 * ↑b) * (↑b / rexp 1) ^ b) * 2 ^ (a + b)))
      = Real.sqrt (↑a + ↑b) * (Stirling.stirlingSeq (a + b) * (√(2 * (↑a + ↑b)) * ((↑a + ↑b) / rexp 1) ^ (a + b))
        / (Stirling.stirlingSeq a * (√(2 * ↑a) * (↑a / rexp 1) ^ a)
            * (Stirling.stirlingSeq b * (√(2 * ↑b) * (↑b / rexp 1) ^ b)) * 2 ^ (a + b)))
      from by ring_nf]
  rw [key]
  rw [hdiff]
  rw [neg_mul]

theorem stirlingSeq_ratio_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Stirling.stirlingSeq (a + b) / (Stirling.stirlingSeq a * Stirling.stirlingSeq b)
      ≤ (Real.sqrt Real.pi)⁻¹ * Real.exp (1 / (12 * ((a : ℝ) + b))) := by
  have h1 : Stirling.stirlingSeq (a + b) ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * ((a : ℝ) + b))) := by
    have h := stirlingSeq_le_sqrt_pi_mul_exp (a + b) (by omega)
    push_cast at h
    exact h
  have h2 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq a := sqrt_pi_le_stirlingSeq' a ha
  have h3 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq b := sqrt_pi_le_stirlingSeq' b hb
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hsa : 0 < Stirling.stirlingSeq a := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) h2
  have hsb : 0 < Stirling.stirlingSeq b := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) h3
  have h4 : Real.sqrt Real.pi * Real.sqrt Real.pi ≤ Stirling.stirlingSeq a * Stirling.stirlingSeq b :=
    mul_le_mul h2 h3 (Real.sqrt_nonneg _) (le_of_lt hsa)
  rw [div_le_iff₀ (by positivity : (0:ℝ) < Stirling.stirlingSeq a * Stirling.stirlingSeq b)]
  have h5 : Real.sqrt Real.pi * Real.exp (1 / (12 * ((a : ℝ) + b))) * Real.sqrt Real.pi
      ≤ Real.exp (1 / (12 * ((a : ℝ) + b))) * (Stirling.stirlingSeq a * Stirling.stirlingSeq b) := by
    nlinarith [h4, Real.exp_pos (1 / (12 * ((a : ℝ) + b)))]
  have h6 : Stirling.stirlingSeq (a + b) * Real.sqrt Real.pi
      ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * ((a : ℝ) + b))) * Real.sqrt Real.pi := by
    nlinarith [h1, Real.sqrt_pos.mpr Real.pi_pos]
  have h7 : (Real.sqrt Real.pi)⁻¹ * Real.exp (1 / (12 * ((a : ℝ) + b)))
      * (Stirling.stirlingSeq a * Stirling.stirlingSeq b) = Real.exp (1 / (12 * ((a : ℝ) + b)))
      * (Stirling.stirlingSeq a * Stirling.stirlingSeq b) / Real.sqrt Real.pi := by ring
  rw [h7]
  rw [le_div_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
  linarith [h5, h6]

theorem stirlingSeq_ratio_ge (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1 / (12 * (a : ℝ))) - 1 / (12 * (b : ℝ)))
      ≤ Stirling.stirlingSeq (a + b) / (Stirling.stirlingSeq a * Stirling.stirlingSeq b) := by
  have h1 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq (a + b) := sqrt_pi_le_stirlingSeq' (a + b) (by omega)
  have h2 : Stirling.stirlingSeq a ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * (a : ℝ))) :=
    stirlingSeq_le_sqrt_pi_mul_exp a ha
  have h3 : Stirling.stirlingSeq b ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * (b : ℝ))) :=
    stirlingSeq_le_sqrt_pi_mul_exp b hb
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hsa : 0 < Stirling.stirlingSeq a := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos)
    (sqrt_pi_le_stirlingSeq' a ha)
  have hsb : 0 < Stirling.stirlingSeq b := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos)
    (sqrt_pi_le_stirlingSeq' b hb)
  have h4 : Stirling.stirlingSeq a * Stirling.stirlingSeq b
      ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * (a : ℝ))) * (Real.sqrt Real.pi * Real.exp (1 / (12 * (b : ℝ)))) :=
    mul_le_mul h2 h3 (le_of_lt hsb) (by positivity)
  have h5 : Real.sqrt Real.pi * Real.exp (1 / (12 * (a : ℝ))) * (Real.sqrt Real.pi * Real.exp (1 / (12 * (b : ℝ))))
      = Real.pi * Real.exp (1 / (12 * (a : ℝ)) + 1 / (12 * (b : ℝ))) := by
    have he : Real.exp (1 / (12 * (a : ℝ))) * Real.exp (1 / (12 * (b : ℝ)))
        = Real.exp (1 / (12 * (a : ℝ)) + 1 / (12 * (b : ℝ))) := (Real.exp_add _ _).symm
    calc Real.sqrt Real.pi * Real.exp (1 / (12 * (a : ℝ))) * (Real.sqrt Real.pi * Real.exp (1 / (12 * (b : ℝ))))
        = (Real.sqrt Real.pi * Real.sqrt Real.pi)
          * (Real.exp (1 / (12 * (a : ℝ))) * Real.exp (1 / (12 * (b : ℝ)))) := by ring
      _ = Real.pi * Real.exp (1 / (12 * (a : ℝ)) + 1 / (12 * (b : ℝ))) := by rw [hsp, he]
  have h6 : (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1 / (12 * (a : ℝ))) - 1 / (12 * (b : ℝ)))
      * (Real.pi * Real.exp (1 / (12 * (a : ℝ)) + 1 / (12 * (b : ℝ)))) = Real.sqrt Real.pi := by
    have he : Real.exp (-(1 / (12 * (a : ℝ))) - 1 / (12 * (b : ℝ)))
        * Real.exp (1 / (12 * (a : ℝ)) + 1 / (12 * (b : ℝ))) = 1 := by
      rw [← Real.exp_add]
      have h0 : -(1 / (12 * (a : ℝ))) - 1 / (12 * (b : ℝ))
          + (1 / (12 * (a : ℝ)) + 1 / (12 * (b : ℝ))) = 0 := by ring
      rw [h0, Real.exp_zero]
    calc (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1 / (12 * (a : ℝ))) - 1 / (12 * (b : ℝ)))
        * (Real.pi * Real.exp (1 / (12 * (a : ℝ)) + 1 / (12 * (b : ℝ))))
        = (Real.sqrt Real.pi)⁻¹ * Real.pi
          * (Real.exp (-(1 / (12 * (a : ℝ))) - 1 / (12 * (b : ℝ)))
            * Real.exp (1 / (12 * (a : ℝ)) + 1 / (12 * (b : ℝ)))) := by ring
      _ = (Real.sqrt Real.pi)⁻¹ * Real.pi * 1 := by rw [he]
      _ = Real.sqrt Real.pi := by
        rw [mul_one]
        rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))]
        exact (Real.mul_self_sqrt Real.pi_pos.le).symm
  have h7 : (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1 / (12 * (a : ℝ))) - 1 / (12 * (b : ℝ)))
      * (Stirling.stirlingSeq a * Stirling.stirlingSeq b)
      ≤ (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1 / (12 * (a : ℝ))) - 1 / (12 * (b : ℝ)))
        * (Real.sqrt Real.pi * Real.exp (1 / (12 * (a : ℝ))) * (Real.sqrt Real.pi * Real.exp (1 / (12 * (b : ℝ))))) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [h5] at h7
  rw [h6] at h7
  rw [le_div_iff₀ (by positivity : (0:ℝ) < Stirling.stirlingSeq a * Stirling.stirlingSeq b)]
  linarith [h1, h7]

/-! ### Polynomial-versus-exponential bounds

Every tail and error estimate below reduces to the single fact that `y ↦ y * exp(-y)`
is bounded by `exp(-1)`: a linear factor against an exponential decay, and (by
squaring) a quadratic factor against the same decay. -/

/-- `x * exp(-(c*x)) ≤ exp(-1)/c` for every real `x` and every `c > 0`. -/
theorem linear_exp_bound (c x : ℝ) (hc : 0 < c) :
    x * Real.exp (-(c * x)) ≤ Real.exp (-1) / c := by
  have h := Real.mul_exp_neg_le_exp_neg_one (c * x)
  rw [le_div_iff₀ hc]
  calc x * Real.exp (-(c * x)) * c = c * x * Real.exp (-(c * x)) := by ring
    _ ≤ Real.exp (-1) := h

/-- `X^2 * exp(-(c*X)) ≤ 4*exp(-2)/c^2` for `X ≥ 0` and `c > 0`. -/
theorem sq_linear_exp_bound (c X : ℝ) (hc : 0 < c) (hX : 0 ≤ X) :
    X ^ 2 * Real.exp (-(c * X)) ≤ 4 * Real.exp (-2) / c ^ 2 := by
  have hc2 : 0 < c / 2 := by linarith
  have h := linear_exp_bound (c / 2) X hc2
  have hnn : 0 ≤ X * Real.exp (-(c / 2 * X)) := mul_nonneg hX (Real.exp_pos _).le
  have hsq := pow_le_pow_left₀ hnn h 2
  have hlhs : (X * Real.exp (-(c / 2 * X))) ^ 2 = X ^ 2 * Real.exp (-(c * X)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hrhs : (Real.exp (-1) / (c / 2)) ^ 2 = 4 * Real.exp (-2) / c ^ 2 := by
    rw [div_pow, ← Real.exp_nat_mul]
    push_cast
    ring
  rw [hlhs, hrhs] at hsq
  exact hsq

/-- `s^2 * gaussianDensity`-type bound: `s^2 * exp(-(s^2)/2) ≤ 2*exp(-1)`. -/
theorem sq_mul_exp_neg_half_sq_le (s : ℝ) :
    s ^ 2 * Real.exp (-(s ^ 2) / 2) ≤ 2 * Real.exp (-1) := by
  have h := linear_exp_bound (1 / 2) (s ^ 2) (by norm_num)
  rw [show -((1:ℝ) / 2 * s ^ 2) = -(s ^ 2) / 2 from by ring] at h
  rw [show Real.exp (-1) / (1 / 2 : ℝ) = 2 * Real.exp (-1) from by ring] at h
  exact h

/-- `s^4 * exp(-(s^2)/2) ≤ 16*exp(-2)`. -/
theorem quartic_mul_exp_neg_half_sq_le (s : ℝ) :
    s ^ 4 * Real.exp (-(s ^ 2) / 2) ≤ 16 * Real.exp (-2) := by
  have h := sq_linear_exp_bound (1 / 2) (s ^ 2) (by norm_num) (sq_nonneg s)
  rw [show -((1:ℝ) / 2 * s ^ 2) = -(s ^ 2) / 2 from by ring] at h
  rw [show (s ^ 2 : ℝ) ^ 2 = s ^ 4 from by ring] at h
  rw [show (4 : ℝ) * Real.exp (-2) / (1 / 2) ^ 2 = 16 * Real.exp (-2) from by ring] at h
  exact h

/-! ### The cubic and quartic Taylor remainders of the logarithm

These specialize Mathlib's generic Taylor-remainder bound for `log(1-x)` to the three
instances the quartic expansion of `gfun` around `0` needs. -/

/-- `log(1+t) = t - t²/2 + δ`, `|δ| ≤ |t|³/(1-|t|)`. -/
theorem log_one_add_bound (t : ℝ) (ht : |t| < 1) :
    |Real.log (1 + t) - (t - t ^ 2 / 2)| ≤ |t| ^ 3 / (1 - |t|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by rwa [abs_neg]) 2
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have heq : Real.log (1 + t) - (t - t ^ 2 / 2) = -t + t ^ 2 / 2 + Real.log (1 + t) := by ring
  rw [heq]; exact h

/-- `log(1-t) = -t - t²/2 + δ`, `|δ| ≤ |t|³/(1-|t|)`. -/
theorem log_one_sub_bound (t : ℝ) (ht : |t| < 1) :
    |Real.log (1 - t) - (-t - t ^ 2 / 2)| ≤ |t| ^ 3 / (1 - |t|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := t) ht 2
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have heq : Real.log (1 - t) - (-t - t ^ 2 / 2) = t + t ^ 2 / 2 + Real.log (1 - t) := by ring
  rw [heq]; exact h

/-- `log(1-t²) = -t² + ε`, `|ε| ≤ t⁴/(1-t²)`. -/
theorem log_one_sub_sq_bound (t : ℝ) (ht : |t| < 1) :
    |Real.log (1 - t ^ 2) - (-(t ^ 2))| ≤ t ^ 4 / (1 - t ^ 2) := by
  have ht2 : |t ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg t)]
    nlinarith [abs_lt.mp ht, sq_abs t]
  have h := Real.abs_log_sub_add_sum_range_le (x := t ^ 2) ht2 1
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have heq : Real.log (1 - t ^ 2) - (-(t ^ 2)) = t ^ 2 + Real.log (1 - t ^ 2) := by ring
  rw [heq]
  have hrw : ((t:ℝ) ^ 2) ^ 2 = t ^ 4 := by ring
  rwa [hrw] at h

/-! ### Pinsker's inequality for the two-point exponent

`gfun t ≥ t²/2` on `(-1,1)`: the relative entropy of the two-point distribution
`(1+t)/2, (1-t)/2` against the fair coin dominates `t²/2`.  The proof is the standard
two-step monotonicity argument: `t ↦ log(1+t) - log(1-t) - 2t` has derivative
`2t²/(1-t²) ≥ 0`, so it is nonnegative on `[0,1)`; feeding that into the derivative of
`gfun t - t²/2`, namely `(1/2)(log(1+t)-log(1-t)) - t`, shows `gfun t - t²/2` is itself
nonnegative on `[0,1)`, and `gfun` is even. -/

theorem log_ratio_deriv (x : ℝ) (hx1 : (1 : ℝ) + x ≠ 0) (hx2 : (1 : ℝ) - x ≠ 0) :
    HasDerivAt (fun y => Real.log (1 + y) - Real.log (1 - y) - 2 * y)
      (1 / (1 + x) + 1 / (1 - x) - 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have hlog1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
    simpa using h1.log hx1
  have h2 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
  have hlog2 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := by
    simpa using h2.log hx2
  have h3 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hsum := (hlog1.sub hlog2).sub h3
  have heq : (1 : ℝ) / (1 + x) - -1 / (1 - x) - 2 = 1 / (1 + x) + 1 / (1 - x) - 2 := by ring
  rwa [heq] at hsum

theorem log_ratio_ge (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * t ≤ Real.log (1 + t) - Real.log (1 - t) := by
  have hmono : MonotoneOn (fun y => Real.log (1 + y) - Real.log (1 - y) - 2 * y)
      (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico (0 : ℝ) 1)
    · apply ContinuousOn.sub
      · apply ContinuousOn.sub
        · apply ContinuousOn.log (by fun_prop)
          intro y hy
          simp only [Set.mem_Ico] at hy
          nlinarith [hy.1, hy.2]
        · apply ContinuousOn.log (by fun_prop)
          intro y hy
          simp only [Set.mem_Ico] at hy
          nlinarith [hy.1, hy.2]
      · fun_prop
    · intro x hx
      rw [interior_Ico] at hx
      simp only [Set.mem_Ioo] at hx
      have hx1 : (1 : ℝ) + x ≠ 0 := by nlinarith [hx.1]
      have hx2 : (1 : ℝ) - x ≠ 0 := by nlinarith [hx.2]
      exact (log_ratio_deriv x hx1 hx2).hasDerivWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      simp only [Set.mem_Ioo] at hx
      have h1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
      have h2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
      have key : 1 / (1 + x) + 1 / (1 - x) - 2 = 2 * x ^ 2 / ((1 + x) * (1 - x)) := by
        field_simp; ring
      rw [key]; positivity
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by constructor <;> norm_num
  have ht : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hres := hmono h0 ht ht0
  simp only at hres
  norm_num at hres
  linarith

theorem gfun_deriv (x : ℝ) (hx1 : (1 : ℝ) + x ≠ 0) (hx2 : (1 : ℝ) - x ≠ 0) :
    HasDerivAt gfun ((1 / 2) * (Real.log (1 + x) - Real.log (1 - x))) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have hlog1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
    simpa using h1.log hx1
  have h2 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
  have hlog2 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := by
    simpa using h2.log hx2
  have hterm1 : HasDerivAt (fun y => (1 + y) / 2 * Real.log (1 + y))
      ((1 / 2) * Real.log (1 + x) + (1 + x) / 2 * (1 / (1 + x))) x := by
    have hu : HasDerivAt (fun y : ℝ => (1 + y) / 2) (1 / 2) x := by
      simpa using h1.div_const 2
    exact hu.mul hlog1
  have hterm2 : HasDerivAt (fun y => (1 - y) / 2 * Real.log (1 - y))
      ((-1 / 2) * Real.log (1 - x) + (1 - x) / 2 * (-1 / (1 - x))) x := by
    have hu : HasDerivAt (fun y : ℝ => (1 - y) / 2) (-1 / 2) x := by
      simpa using h2.div_const 2
    exact hu.mul hlog2
  have hsum := hterm1.add hterm2
  have heq1 : (1 + x) / 2 * (1 / (1 + x)) = 1 / 2 := by field_simp
  have heq2 : (1 - x) / 2 * (-1 / (1 - x)) = -1 / 2 := by field_simp
  rw [heq1, heq2] at hsum
  have heq3 : (1 : ℝ) / 2 * Real.log (1 + x) + 1 / 2 + ((-1 / 2) * Real.log (1 - x) + -1 / 2)
      = (1 / 2) * (Real.log (1 + x) - Real.log (1 - x)) := by ring
  rw [heq3] at hsum
  exact hsum

theorem half_sq_deriv (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ (2 - 1)) x := hasDerivAt_pow 2 x
  have h2 := h1.div_const 2
  norm_num at h2
  convert h2 using 1

theorem h_deriv (x : ℝ) (hx1 : (1 : ℝ) + x ≠ 0) (hx2 : (1 : ℝ) - x ≠ 0) :
    HasDerivAt (fun y => gfun y - y ^ 2 / 2)
      ((1 / 2) * (Real.log (1 + x) - Real.log (1 - x)) - x) x :=
  (gfun_deriv x hx1 hx2).sub (half_sq_deriv x)

theorem gfun_ge_half_sq_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t ^ 2 / 2 ≤ gfun t := by
  have hmono : MonotoneOn (fun y => gfun y - y ^ 2 / 2) (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico (0 : ℝ) 1)
    · have hcont : ContinuousOn gfun (Set.Ico (0 : ℝ) 1) := by
        apply ContinuousOn.add
        · apply ContinuousOn.mul (by fun_prop)
          apply ContinuousOn.log (by fun_prop)
          intro y hy
          simp only [Set.mem_Ico] at hy
          nlinarith [hy.1, hy.2]
        · apply ContinuousOn.mul (by fun_prop)
          apply ContinuousOn.log (by fun_prop)
          intro y hy
          simp only [Set.mem_Ico] at hy
          nlinarith [hy.1, hy.2]
      exact hcont.sub (by fun_prop)
    · intro x hx
      rw [interior_Ico] at hx
      simp only [Set.mem_Ioo] at hx
      have hx1 : (1 : ℝ) + x ≠ 0 := by nlinarith [hx.1]
      have hx2 : (1 : ℝ) - x ≠ 0 := by nlinarith [hx.2]
      exact (h_deriv x hx1 hx2).hasDerivWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      simp only [Set.mem_Ioo] at hx
      have hlr := log_ratio_ge x hx.1.le hx.2
      linarith
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by constructor <;> norm_num
  have htm : t ∈ Set.Ico (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hmn := hmono h0 htm ht0
  simp only [gfun] at hmn ⊢
  norm_num at hmn ⊢
  linarith

/-- `gfun` is even. -/
theorem gfun_even (t : ℝ) : gfun (-t) = gfun t := by
  show (1 + -t) / 2 * Real.log (1 + -t) + (1 - -t) / 2 * Real.log (1 - -t) = gfun t
  rw [show (1 : ℝ) + -t = 1 - t from by ring, show (1 : ℝ) - -t = 1 + t from by ring]
  unfold gfun
  ring

/-- **Pinsker's inequality for the two-point exponent.** -/
theorem gfun_ge_half_sq (t : ℝ) (ht : |t| < 1) : t ^ 2 / 2 ≤ gfun t := by
  by_cases h : 0 ≤ t
  · exact gfun_ge_half_sq_nonneg t h (abs_lt.mp ht).2
  · have h' : t < 0 := not_le.mp h
    have hnt : 0 ≤ -t := by linarith
    have hnt1 : -t < 1 := by have := (abs_lt.mp ht).1; linarith
    have hkey := gfun_ge_half_sq_nonneg (-t) hnt hnt1
    rw [gfun_even] at hkey
    nlinarith [hkey]

/-! ### The quartic expansion of `gfun` around `0`

`gfun t = (1/2) log(1-t²) + t · artanh(t)`, and each piece is controlled by the cubic and
quartic Taylor remainders above; the linear and cubic terms cancel exactly, leaving a
quartic error. -/

theorem abs_sub_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h : a - b = a + (-b) := by ring
  rw [h]
  calc |a + -b| ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

theorem gfun_eq_half_log_add_t_half_diff (t : ℝ) (ht : |t| < 1) :
    gfun t = (1 / 2) * Real.log (1 - t ^ 2)
      + t * ((1 / 2) * (Real.log (1 + t) - Real.log (1 - t))) := by
  have h1 : (1 : ℝ) + t ≠ 0 := by nlinarith [abs_lt.mp ht]
  have h2 : (1 : ℝ) - t ≠ 0 := by nlinarith [abs_lt.mp ht]
  have hlog : Real.log (1 - t ^ 2) = Real.log (1 + t) + Real.log (1 - t) := by
    rw [show (1 : ℝ) - t ^ 2 = (1 + t) * (1 - t) from by ring, Real.log_mul h1 h2]
  rw [hlog]
  unfold gfun
  ring

/-- **The quartic bound on `gfun` near `0`.** -/
theorem gfun_quartic_bound (t : ℝ) (ht : |t| ≤ 1 / 2) :
    |gfun t - t ^ 2 / 2| ≤ (8 / 3) * t ^ 4 := by
  have ht1 : |t| < 1 := by linarith
  have heq := gfun_eq_half_log_add_t_half_diff t ht1
  have hA := log_one_sub_sq_bound t ht1
  have hδ1 := log_one_add_bound t ht1
  have hδ2 := log_one_sub_bound t ht1
  have hgt : gfun t - t ^ 2 / 2
      = (1 / 2) * (Real.log (1 - t ^ 2) - (-(t ^ 2)))
        + t * ((1 / 2) * ((Real.log (1 + t) - (t - t ^ 2 / 2))
          - (Real.log (1 - t) - (-t - t ^ 2 / 2)))) := by
    rw [heq]; ring
  rw [hgt]
  have htabs : |t| ≤ (1 : ℝ) / 2 := ht
  have ht2 : t ^ 2 ≤ 1 / 4 := by
    have hsq : (t : ℝ) ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [hsq]
    nlinarith [mul_le_mul htabs htabs (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
  have h1mt2 : (1 : ℝ) - t ^ 2 ≥ 3 / 4 := by linarith
  have h1mabst : (1 : ℝ) - |t| ≥ 1 / 2 := by linarith [htabs]
  have step1 : |(1 / 2) * (Real.log (1 - t ^ 2) - (-(t ^ 2)))| ≤ (1 / 2) * (t ^ 4 / (1 - t ^ 2)) := by
    rw [abs_mul, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
    exact mul_le_mul_of_nonneg_left hA (by norm_num)
  have step2 : |t * ((1 / 2) * ((Real.log (1 + t) - (t - t ^ 2 / 2))
        - (Real.log (1 - t) - (-t - t ^ 2 / 2))))|
      ≤ |t| * ((1 / 2) * (2 * (|t| ^ 3 / (1 - |t|)))) := by
    rw [abs_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc |(Real.log (1 + t) - (t - t ^ 2 / 2)) - (Real.log (1 - t) - (-t - t ^ 2 / 2))|
        ≤ |Real.log (1 + t) - (t - t ^ 2 / 2)| + |Real.log (1 - t) - (-t - t ^ 2 / 2)| :=
          abs_sub_abs_add _ _
      _ ≤ |t| ^ 3 / (1 - |t|) + |t| ^ 3 / (1 - |t|) := by linarith [hδ1, hδ2]
      _ = 2 * (|t| ^ 3 / (1 - |t|)) := by ring
  have step3 :
      |(1 / 2) * (Real.log (1 - t ^ 2) - (-(t ^ 2)))
        + t * ((1 / 2) * ((Real.log (1 + t) - (t - t ^ 2 / 2))
          - (Real.log (1 - t) - (-t - t ^ 2 / 2))))|
      ≤ (1 / 2) * (t ^ 4 / (1 - t ^ 2)) + |t| * ((1 / 2) * (2 * (|t| ^ 3 / (1 - |t|)))) :=
    le_trans (abs_add_le _ _) (by linarith [step1, step2])
  refine le_trans step3 ?_
  have hpos : (0 : ℝ) < 1 - t ^ 2 := by linarith
  have hpos2 : (0 : ℝ) < 1 - |t| := by linarith
  have ht4eq : t ^ 4 = |t| ^ 4 := by
    have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    nlinarith [hsq]
  have hstep1 : t ^ 4 / (1 - t ^ 2) ≤ (4 / 3) * t ^ 4 := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg (sq_nonneg (t ^ 2)) (by linarith [ht2] : (0 : ℝ) ≤ 1 - 4 * t ^ 2)]
  have hsub1 : (1 / 2 : ℝ) * (t ^ 4 / (1 - t ^ 2)) ≤ (2 / 3) * t ^ 4 := by linarith [hstep1]
  have heq2 : |t| * ((1 / 2) * (2 * (|t| ^ 3 / (1 - |t|)))) = |t| ^ 4 / (1 - |t|) := by
    field_simp
  have hstep2 : |t| ^ 4 / (1 - |t|) ≤ 2 * |t| ^ 4 := by
    rw [div_le_iff₀ hpos2]
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg t) 4) (by linarith [htabs] : (0 : ℝ) ≤ 1 - 2 * |t|)]
  have hsub2 : |t| * ((1 / 2) * (2 * (|t| ^ 3 / (1 - |t|)))) ≤ 2 * t ^ 4 := by
    rw [heq2, ht4eq]
    linarith [hstep2]
  linarith [hsub1, hsub2]


/-! ### Region 1: the central range `|j| ≤ m/2` -/
/-! ### Region 1: the central range `|j| \u2264 m/2` -/

theorem m_ge_two_of_region1 (m : ℕ) (hm : 1 ≤ m) (j : ℤ) (hj : j ≡ (m : ℤ) [ZMOD 2])
    (hjR : |(j:ℝ)| ≤ (m:ℝ) / 2) : 2 ≤ m := by
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · exfalso
    have hm1 : m = 1 := by omega
    have h1 : |(j:ℝ)| ≤ (1:ℝ)/2 := by rw [hm1] at hjR; exact_mod_cast hjR
    have hjz : |(j:ℝ)| < 1 := by linarith
    have h2 : |j| < 1 := by exact_mod_cast hjz
    have hb := abs_lt.mp h2
    have hj0 : j = 0 := by omega
    rw [hj0, hm1] at hj
    simp [Int.ModEq] at hj
  · exact hge


theorem ab_facts_region1 (m : ℕ) (hm2 : 2 ≤ m) (j : ℤ) (hj : j ≡ (m : ℤ) [ZMOD 2])
    (hjR : |(j:ℝ)| ≤ (m:ℝ) / 2) :
    1 ≤ (((m:ℤ)+j)/2).toNat ∧ 1 ≤ (((m:ℤ)-j)/2).toNat ∧
    (((m:ℤ)+j)/2).toNat + (((m:ℤ)-j)/2).toNat = m ∧
    (m:ℝ)/4 ≤ ((((m:ℤ)+j)/2).toNat : ℝ) ∧ (m:ℝ)/4 ≤ ((((m:ℤ)-j)/2).toNat : ℝ) ∧
    |(j:ℝ)| ≤ (m:ℝ) - 2 := by
  have hjZ : 2 * |j| ≤ (m:ℤ) := by
    have h1 : (2:ℝ) * |(j:ℝ)| ≤ (m:ℝ) := by linarith [hjR]
    have h2 : ((2 * |j| : ℤ) : ℝ) ≤ ((m:ℤ):ℝ) := by push_cast; linarith [h1]
    exact_mod_cast h2
  have hl : -|j| ≤ j := neg_abs_le j
  have hr : j ≤ |j| := le_abs_self j
  have hdvd2 : (2 : ℤ) ∣ ((m : ℤ) - j) := Int.ModEq.dvd hj
  have hdvd : (2 : ℤ) ∣ ((m : ℤ) + j) := by omega
  set a : ℕ := (((m:ℤ)+j)/2).toNat with ha
  set b : ℕ := (((m:ℤ)-j)/2).toNat with hb
  have hja : ((a:ℤ)) = ((m:ℤ)+j)/2 := by rw [ha]; exact Int.toNat_of_nonneg (by omega)
  have hjb : ((b:ℤ)) = ((m:ℤ)-j)/2 := by rw [hb]; exact Int.toNat_of_nonneg (by omega)
  have ha1 : 1 ≤ a := by
    have h : (1:ℤ) ≤ (a:ℤ) := by rw [hja]; omega
    exact_mod_cast h
  have hb1 : 1 ≤ b := by
    have h : (1:ℤ) ≤ (b:ℤ) := by rw [hjb]; omega
    exact_mod_cast h
  have hsum : a + b = m := by
    have h : (a:ℤ) + (b:ℤ) = (m:ℤ) := by rw [hja, hjb]; omega
    exact_mod_cast h
  have ha4 : (m:ℤ) ≤ 4 * (a:ℤ) := by rw [hja]; omega
  have hb4 : (m:ℤ) ≤ 4 * (b:ℤ) := by rw [hjb]; omega
  have hj1Z : |j| ≤ (m:ℤ) - 2 := by
    rcases abs_cases j with ⟨heq, _⟩ | ⟨heq, _⟩ <;> omega
  refine ⟨ha1, hb1, hsum, ?_, ?_, ?_⟩
  · have h : (m:ℝ) ≤ 4 * (a:ℝ) := by exact_mod_cast ha4
    linarith
  · have h : (m:ℝ) ≤ 4 * (b:ℝ) := by exact_mod_cast hb4
    linarith
  · exact_mod_cast hj1Z

theorem stirling_ratio_upper_m (m a b : ℕ) (hab : a + b = m) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 1 ≤ m) :
    Stirling.stirlingSeq m / (Stirling.stirlingSeq a * Stirling.stirlingSeq b)
      ≤ (Real.sqrt Real.pi)⁻¹ * (1 + 1 / (6 * (m:ℝ))) := by
  have h1 := stirlingSeq_ratio_le a b ha hb
  have habR : (a:ℝ) + b = m := by exact_mod_cast hab
  rw [hab, habR] at h1
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  have hxle1 : |(1:ℝ)/(12*(m:ℝ))| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    linarith
  have h2 := abs_exp_sub_one_le_two_mul (1/(12*(m:ℝ))) hxle1
  have hexp_nonneg : (0:ℝ) ≤ 1/(12*(m:ℝ)) := by positivity
  rw [abs_of_nonneg hexp_nonneg] at h2
  have h3 : Real.exp (1/(12*(m:ℝ))) - 1 ≤ 2 * (1/(12*(m:ℝ))) := by
    have := abs_le.mp h2
    linarith [this.2]
  have h4 : Real.exp (1/(12*(m:ℝ))) ≤ 1 + 1/(6*(m:ℝ)) := by
    have heq : 2 * (1/(12*(m:ℝ))) = 1/(6*(m:ℝ)) := by ring
    linarith [h3, heq.le, heq.ge]
  have hsqrtpi_pos : (0:ℝ) < (Real.sqrt Real.pi)⁻¹ := by positivity
  calc Stirling.stirlingSeq m / (Stirling.stirlingSeq a * Stirling.stirlingSeq b)
      ≤ (Real.sqrt Real.pi)⁻¹ * Real.exp (1/(12*(m:ℝ))) := h1
    _ ≤ (Real.sqrt Real.pi)⁻¹ * (1 + 1/(6*(m:ℝ))) := by
        apply mul_le_mul_of_nonneg_left h4 hsqrtpi_pos.le

theorem stirling_ratio_lower_m (m a b : ℕ) (hab : a + b = m) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : 1 ≤ m) (ha4 : (m:ℝ) ≤ 4 * (a:ℝ)) (hb4 : (m:ℝ) ≤ 4 * (b:ℝ)) :
    (Real.sqrt Real.pi)⁻¹ * (1 - 2 / (3 * (m:ℝ)))
      ≤ Stirling.stirlingSeq m / (Stirling.stirlingSeq a * Stirling.stirlingSeq b) := by
  have h1 := stirlingSeq_ratio_ge a b ha hb
  rw [hab] at h1
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hae : 1/(12*(a:ℝ)) ≤ 1/(3*(m:ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [ha4]
  have hbe : 1/(12*(b:ℝ)) ≤ 1/(3*(m:ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hb4]
  have hcomb : 1/(12*(a:ℝ)) + 1/(12*(b:ℝ)) ≤ 2/(3*(m:ℝ)) := by
    have heq : 2/(3*(m:ℝ)) = 1/(3*(m:ℝ)) + 1/(3*(m:ℝ)) := by ring
    linarith [hae, hbe, heq.ge, heq.le]
  have hexpmono : Real.exp (-(2/(3*(m:ℝ)))) ≤ Real.exp (-(1/(12*(a:ℝ))) - 1/(12*(b:ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith [hcomb]
  have h4 : (1:ℝ) - 2/(3*(m:ℝ)) ≤ Real.exp (-(2/(3*(m:ℝ)))) := by
    have := Real.add_one_le_exp (-(2/(3*(m:ℝ))))
    linarith [this]
  have hsqrtpi_pos : (0:ℝ) < (Real.sqrt Real.pi)⁻¹ := by positivity
  calc (Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ)))
      ≤ (Real.sqrt Real.pi)⁻¹ * Real.exp (-(2/(3*(m:ℝ)))) :=
        mul_le_mul_of_nonneg_left h4 hsqrtpi_pos.le
    _ ≤ (Real.sqrt Real.pi)⁻¹ * Real.exp (-(1/(12*(a:ℝ))) - 1/(12*(b:ℝ))) :=
        mul_le_mul_of_nonneg_left hexpmono hsqrtpi_pos.le
    _ ≤ Stirling.stirlingSeq m / (Stirling.stirlingSeq a * Stirling.stirlingSeq b) := h1

theorem prefactor_bound (t : ℝ) (ht : |t| ≤ 1/2) :
    |Real.sqrt 2 / Real.sqrt (1 - t^2) - Real.sqrt 2| ≤ 2 * t^2 := by
  have ht2 : t^2 ≤ 1/4 := by nlinarith [sq_abs t, abs_nonneg t, ht]
  have hxge : (0:ℝ) ≤ 1 - t^2 := by linarith
  have hxle1 : (1:ℝ) - t^2 ≤ 1 := by nlinarith [sq_nonneg t]
  have hpos : (0:ℝ) < 1 - t^2 := by linarith
  have h34 : (1:ℝ) - t^2 ≥ 3/4 := by linarith
  have hsqrt_ge : (1 - t^2) ≤ Real.sqrt (1 - t^2) :=
    by nlinarith [Real.sq_sqrt hxge, Real.sqrt_nonneg (1-t^2), sq_nonneg (Real.sqrt (1-t^2) - 1)]
  have hsqrt_le1 : Real.sqrt (1-t^2) ≤ 1 := by
    nlinarith [Real.sq_sqrt hxge, Real.sqrt_nonneg (1-t^2), sq_nonneg (Real.sqrt (1-t^2) - 1)]
  have hsqrt_ge34 : Real.sqrt (1-t^2) ≥ 3/4 := le_trans h34 hsqrt_ge
  have hsqrt_pos : (0:ℝ) < Real.sqrt (1-t^2) := by linarith
  have hnum : (0:ℝ) ≤ 1 - Real.sqrt (1-t^2) := by linarith [hsqrt_le1]
  have hnumle : 1 - Real.sqrt (1-t^2) ≤ t^2 := by linarith [hsqrt_ge]
  have hdiffeq : Real.sqrt 2 / Real.sqrt (1-t^2) - Real.sqrt 2
      = Real.sqrt 2 * (1 - Real.sqrt (1-t^2)) / Real.sqrt (1-t^2) := by
    field_simp
  have hdiffnn : (0:ℝ) ≤ Real.sqrt 2 * (1 - Real.sqrt (1-t^2)) / Real.sqrt (1-t^2) := by
    positivity
  rw [hdiffeq, abs_of_nonneg hdiffnn]
  rw [div_le_iff₀ hsqrt_pos]
  have hsqrt2 : Real.sqrt 2 ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
  calc Real.sqrt 2 * (1 - Real.sqrt (1-t^2)) ≤ (3/2) * t^2 := by
        apply mul_le_mul hsqrt2 hnumle hnum (by norm_num)
    _ ≤ 2 * t^2 * Real.sqrt (1-t^2) := by nlinarith [hsqrt_ge34, sq_nonneg t]

theorem prefactor_ge (t : ℝ) (ht : |t| < 1) :
    Real.sqrt 2 ≤ Real.sqrt 2 / Real.sqrt (1 - t^2) := by
  have hxge : (0:ℝ) ≤ 1 - t^2 := by nlinarith [sq_abs t, abs_lt.mp ht]
  have hsqrt_le1 : Real.sqrt (1-t^2) ≤ 1 := by
    nlinarith [Real.sq_sqrt hxge, Real.sqrt_nonneg (1-t^2), sq_nonneg (Real.sqrt (1-t^2) - 1)]
  have hpos : (0:ℝ) < 1 - t^2 := by nlinarith [sq_abs t, abs_lt.mp ht]
  have hsqrt_pos : (0:ℝ) < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr hpos
  rw [le_div_iff₀ hsqrt_pos]
  nlinarith [Real.sqrt_nonneg (2:ℝ), hsqrt_le1]


theorem gaussianDensity_two_eq (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (j : ℤ) (ht : t = (j:ℝ)/(m:ℝ)) :
    2 * gaussianDensity ((j:ℝ) / Real.sqrt m)
      = Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ) * t^2 / 2) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hs2 : ((j:ℝ) / Real.sqrt (m:ℝ))^2 = (m:ℝ) * t^2 := by
    rw [div_pow, Real.sq_sqrt hm0.le, ht]
    field_simp
  unfold gaussianDensity
  rw [hs2]
  have hconst : 2 * (Real.sqrt (2*Real.pi))⁻¹ = Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [show -((m:ℝ) * t^2) / 2 = -((m:ℝ)*t^2/2) from by ring]
  rw [← hconst]
  ring


theorem region1_A3_bounds (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (htabs : |t| ≤ 1/2) :
    Real.exp (-(m:ℝ) * gfun t) ≤ Real.exp (-(m:ℝ)*t^2/2) ∧
    Real.exp (-(m:ℝ)*t^2/2) * (1 - (8/3)*(m:ℝ)*t^4) ≤ Real.exp (-(m:ℝ) * gfun t) := by
  have htabs1 : |t| < 1 := by linarith
  have hgfun_lb := gfun_ge_half_sq t htabs1
  have hgfun_ub := gfun_quartic_bound t htabs
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith [hgfun_lb, hm0.le]
  · have hub : gfun t - t^2/2 ≤ (8/3)*t^4 := (abs_le.mp hgfun_ub).2
    have hstep : Real.exp (-(m:ℝ)*t^2/2 - (8/3)*(m:ℝ)*t^4) ≤ Real.exp (-(m:ℝ)*gfun t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hub, hm0.le]
    have hstep2 : Real.exp (-(m:ℝ)*t^2/2) * (1-(8/3)*(m:ℝ)*t^4)
        ≤ Real.exp (-(m:ℝ)*t^2/2 - (8/3)*(m:ℝ)*t^4) := by
      rw [show -(m:ℝ)*t^2/2 - (8/3)*(m:ℝ)*t^4 = -(m:ℝ)*t^2/2 + (-((8/3)*(m:ℝ)*t^4)) from by ring,
        Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hae := Real.add_one_le_exp (-((8/3)*(m:ℝ)*t^4))
      linarith [hae]
    linarith [hstep, hstep2]


theorem key_bound1 (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    t^2 * Real.exp (-(m:ℝ)*t^2/2) ≤ 2 * Real.exp (-1) / m := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  set s := t * Real.sqrt (m:ℝ) with hsdef
  have hs2 : s^2 = (m:ℝ) * t^2 := by
    rw [hsdef, mul_pow, Real.sq_sqrt hm0.le]; ring
  have hkey := sq_mul_exp_neg_half_sq_le s
  rw [hs2] at hkey
  have heq : -((m:ℝ)*t^2)/2 = -(m:ℝ)*t^2/2 := by ring
  rw [heq] at hkey
  rw [le_div_iff₀ hm0]
  nlinarith [hkey, Real.exp_pos (-(m:ℝ)*t^2/2)]

theorem key_bound2 (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    (m:ℝ) * t^4 * Real.exp (-(m:ℝ)*t^2/2) ≤ 16 * Real.exp (-2) / m := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  set s := t * Real.sqrt (m:ℝ) with hsdef
  have hs2 : s^2 = (m:ℝ) * t^2 := by
    rw [hsdef, mul_pow, Real.sq_sqrt hm0.le]; ring
  have hs4 : s^4 = (m:ℝ)^2 * t^4 := by
    have : s^4 = (s^2)^2 := by ring
    rw [this, hs2]; ring
  have hkey := quartic_mul_exp_neg_half_sq_le s
  rw [hs4] at hkey
  have heq : -(s^2)/2 = -(m:ℝ)*t^2/2 := by rw [hs2]; ring
  rw [heq] at hkey
  rw [le_div_iff₀ hm0]
  have hexp_pos := Real.exp_pos (-(m:ℝ)*t^2/2)
  have hm2 : (m:ℝ)^2 = (m:ℝ) * (m:ℝ) := by ring
  rw [hm2] at hkey
  nlinarith [hkey, hexp_pos, hm0]


theorem region1_upper_diff (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    ((Real.sqrt Real.pi)⁻¹ * (1 + 1/(6*(m:ℝ)))) * (Real.sqrt 2 + 2*t^2)
        * Real.exp (-(m:ℝ)*t^2/2)
      - Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)*t^2/2)
    ≤ ((Real.sqrt Real.pi)⁻¹ * (4*Real.exp (-1) + Real.sqrt 2/6 + 2*Real.exp (-1)/3)) / (m:ℝ) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hkey1 := key_bound1 m hm t
  have hpi_inv_nn : (0:ℝ) ≤ (Real.sqrt Real.pi)⁻¹ := by positivity
  have hE_le_one : Real.exp (-(m:ℝ)*t^2/2) ≤ 1 := by
    have hle0 : -(m:ℝ)*t^2/2 ≤ 0 := by nlinarith [sq_nonneg t, hm0.le]
    calc Real.exp (-(m:ℝ)*t^2/2) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle0
      _ = 1 := Real.exp_zero
  have hexpand :
      ((Real.sqrt Real.pi)⁻¹ * (1 + 1/(6*(m:ℝ)))) * (Real.sqrt 2 + 2*t^2)
          * Real.exp (-(m:ℝ)*t^2/2)
        - Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)*t^2/2)
      = (Real.sqrt Real.pi)⁻¹ * (2*(t^2*Real.exp (-(m:ℝ)*t^2/2))
          + (Real.sqrt 2/(6*(m:ℝ)))*Real.exp (-(m:ℝ)*t^2/2)
          + (1/(3*(m:ℝ)))*(t^2*Real.exp (-(m:ℝ)*t^2/2))) := by ring
  rw [hexpand]
  have hb1 : 2*(t^2*Real.exp (-(m:ℝ)*t^2/2)) ≤ 4*Real.exp (-1)/(m:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hkey1 (by norm_num : (0:ℝ) ≤ 2)
    calc 2*(t^2*Real.exp (-(m:ℝ)*t^2/2)) ≤ 2*(2*Real.exp (-1)/(m:ℝ)) := h
      _ = 4*Real.exp (-1)/(m:ℝ) := by ring
  have hb2 : (Real.sqrt 2/(6*(m:ℝ)))*Real.exp (-(m:ℝ)*t^2/2) ≤ Real.sqrt 2/(6*(m:ℝ)) := by
    nlinarith [hE_le_one, (by positivity : (0:ℝ) ≤ Real.sqrt 2/(6*(m:ℝ)))]
  have hb3 : (1/(3*(m:ℝ)))*(t^2*Real.exp (-(m:ℝ)*t^2/2)) ≤ 2*Real.exp (-1)/(3*(m:ℝ)) := by
    have h1 : (1/(3*(m:ℝ)))*(t^2*Real.exp (-(m:ℝ)*t^2/2))
        ≤ (1/(3*(m:ℝ)))*(2*Real.exp (-1)/(m:ℝ)) :=
      mul_le_mul_of_nonneg_left hkey1 (by positivity)
    have h2 : (1/(3*(m:ℝ)))*(2*Real.exp (-1)/(m:ℝ)) ≤ 2*Real.exp (-1)/(3*(m:ℝ)) := by
      rw [show (1/(3*(m:ℝ)))*(2*Real.exp (-1)/(m:ℝ)) = 2*Real.exp (-1)/(3*(m:ℝ)^2) from by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (Real.exp_pos (-1:ℝ)).le
        (by nlinarith [hm1] : (0:ℝ) ≤ (m:ℝ)^2 - (m:ℝ))]
    linarith [h1, h2]
  have hsum1 : 2*(t^2*Real.exp (-(m:ℝ)*t^2/2)) + (Real.sqrt 2/(6*(m:ℝ)))*Real.exp (-(m:ℝ)*t^2/2)
        + (1/(3*(m:ℝ)))*(t^2*Real.exp (-(m:ℝ)*t^2/2))
      ≤ 4*Real.exp (-1)/(m:ℝ) + Real.sqrt 2/(6*(m:ℝ)) + 2*Real.exp (-1)/(3*(m:ℝ)) := by
    linarith [hb1, hb2, hb3]
  have hfin := mul_le_mul_of_nonneg_left hsum1 hpi_inv_nn
  rw [show (Real.sqrt Real.pi)⁻¹ * (4*Real.exp (-1)/(m:ℝ) + Real.sqrt 2/(6*(m:ℝ))
        + 2*Real.exp (-1)/(3*(m:ℝ)))
      = ((Real.sqrt Real.pi)⁻¹ * (4*Real.exp (-1) + Real.sqrt 2/6 + 2*Real.exp (-1)/3)) / (m:ℝ)
      from by ring] at hfin
  exact hfin

theorem region1_lower_diff (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)*t^2/2)
      - ((Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ)))) * Real.sqrt 2
          * (Real.exp (-(m:ℝ)*t^2/2) * (1 - (8/3)*(m:ℝ)*t^4))
    ≤ (Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2/3 + 128*Real.exp (-2)/3)) / (m:ℝ) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hkey2 := key_bound2 m hm t
  have hconst_nn : (0:ℝ) ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ := by positivity
  have hE_le_one : Real.exp (-(m:ℝ)*t^2/2) ≤ 1 := by
    have hle0 : -(m:ℝ)*t^2/2 ≤ 0 := by nlinarith [sq_nonneg t, hm0.le]
    calc Real.exp (-(m:ℝ)*t^2/2) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle0
      _ = 1 := Real.exp_zero
  have hE_nn : (0:ℝ) ≤ Real.exp (-(m:ℝ)*t^2/2) := (Real.exp_pos _).le
  have hmt4_nn : (0:ℝ) ≤ (m:ℝ)*t^4 := by positivity
  have hdrop :
      Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)*t^2/2)
        - ((Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ)))) * Real.sqrt 2
            * (Real.exp (-(m:ℝ)*t^2/2) * (1 - (8/3)*(m:ℝ)*t^4))
      ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹
          * ((2/(3*(m:ℝ)))*Real.exp (-(m:ℝ)*t^2/2)
              + (8/3)*((m:ℝ)*t^4*Real.exp (-(m:ℝ)*t^2/2))) := by
    have hcross_nn : (0:ℝ) ≤ (2/(3*(m:ℝ))) * ((8/3)*((m:ℝ)*t^4)) := by positivity
    nlinarith [hcross_nn, mul_nonneg hconst_nn hE_nn,
      mul_le_mul_of_nonneg_left hcross_nn hE_nn]
  refine le_trans hdrop ?_
  have hb1 : (2/(3*(m:ℝ)))*Real.exp (-(m:ℝ)*t^2/2) ≤ 2/(3*(m:ℝ)) := by
    nlinarith [hE_le_one, (by positivity : (0:ℝ) ≤ 2/(3*(m:ℝ)))]
  have hb2 : (8/3)*((m:ℝ)*t^4*Real.exp (-(m:ℝ)*t^2/2)) ≤ (8/3)*(16*Real.exp (-2)/(m:ℝ)) :=
    mul_le_mul_of_nonneg_left hkey2 (by norm_num)
  have hb2' : (8/3)*(16*Real.exp (-2)/(m:ℝ)) = 128*Real.exp (-2)/(3*(m:ℝ)) := by ring
  rw [hb2'] at hb2
  have hsum : (2/(3*(m:ℝ)))*Real.exp (-(m:ℝ)*t^2/2)
        + (8/3)*((m:ℝ)*t^4*Real.exp (-(m:ℝ)*t^2/2))
      ≤ 2/(3*(m:ℝ)) + 128*Real.exp (-2)/(3*(m:ℝ)) := by linarith [hb1, hb2]
  have hfin := mul_le_mul_of_nonneg_left hsum hconst_nn
  rw [show Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2/(3*(m:ℝ)) + 128*Real.exp (-2)/(3*(m:ℝ)))
        = (Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2/3 + 128*Real.exp (-2)/3)) / (m:ℝ)
      from by ring] at hfin
  exact hfin

/-- **The region-1 (central range) bound.** -/
theorem region1_bound (m : ℕ) (hm : 1 ≤ m) (j : ℤ) (hj : j ≡ (m:ℤ) [ZMOD 2])
    (hjR : |(j:ℝ)| ≤ (m:ℝ)/2) :
    |Real.sqrt m * binomPMF m j - 2 * gaussianDensity ((j:ℝ)/Real.sqrt m)|
      ≤ ((Real.sqrt Real.pi)⁻¹ * (4*Real.exp (-1) + Real.sqrt 2/6 + 2*Real.exp (-1)/3)
          + Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2/3 + 128*Real.exp (-2)/3)) / (m:ℝ) := by
  have hm2 := m_ge_two_of_region1 m hm j hj hjR
  obtain ⟨ha1, hb1, hab, ha4, hb4, hj1⟩ := ab_facts_region1 m hm2 j hj hjR
  have heq := sqrt_mul_binomPMF_eq m hm j hj (by exact_mod_cast hj1)
  set t := (j:ℝ)/(m:ℝ) with htdef
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have htabs : |t| ≤ 1/2 := by
    rw [htdef, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    linarith [hjR]
  have htabs1 : |t| < 1 := by linarith
  -- name the three factors
  set A1 := Stirling.stirlingSeq m
      / (Stirling.stirlingSeq (((m:ℤ)+j)/2).toNat * Stirling.stirlingSeq (((m:ℤ)-j)/2).toNat)
    with hA1def
  set A2 := Real.sqrt 2 / Real.sqrt (1 - t^2) with hA2def
  set A3 := Real.exp (-(m:ℝ) * gfun t) with hA3def
  have hSRle : A1 ≤ (Real.sqrt Real.pi)⁻¹ * (1 + 1/(6*(m:ℝ))) :=
    stirling_ratio_upper_m m _ _ hab ha1 hb1 hm
  have hSRge : (Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ))) ≤ A1 :=
    stirling_ratio_lower_m m _ _ hab ha1 hb1 hm (by linarith [ha4]) (by linarith [hb4])
  have hA2le : A2 ≤ Real.sqrt 2 + 2*t^2 := by
    have h := prefactor_bound t htabs
    have hge := prefactor_ge t htabs1
    rw [abs_of_nonneg (by linarith [hge] : (0:ℝ) ≤ A2 - Real.sqrt 2)] at h
    linarith [h]
  have hA2ge : Real.sqrt 2 ≤ A2 := prefactor_ge t htabs1
  obtain ⟨hA3le, hA3ge⟩ := region1_A3_bounds m hm t htabs
  have hL1nn : (0:ℝ) ≤ (Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ))) := by
    have : (2:ℝ)/(3*(m:ℝ)) ≤ 2/3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hpi : (0:ℝ) ≤ (Real.sqrt Real.pi)⁻¹ := by positivity
    nlinarith [hpi, this]
  have hA1nn : (0:ℝ) ≤ A1 := le_trans hL1nn hSRge
  have hA2nn : (0:ℝ) ≤ A2 := le_trans (Real.sqrt_nonneg 2) hA2ge
  have hA3nn : (0:ℝ) ≤ A3 := (Real.exp_pos _).le
  -- UPPER bound on A1*A2*A3
  have hUpper : A1*A2*A3 ≤
      ((Real.sqrt Real.pi)⁻¹ * (1 + 1/(6*(m:ℝ)))) * (Real.sqrt 2 + 2*t^2)
        * Real.exp (-(m:ℝ)*t^2/2) := by
    have hstep1 : A1*A2 ≤ ((Real.sqrt Real.pi)⁻¹ * (1 + 1/(6*(m:ℝ)))) * (Real.sqrt 2 + 2*t^2) :=
      mul_le_mul hSRle hA2le hA2nn (by positivity)
    have hstep1nn : (0:ℝ) ≤ ((Real.sqrt Real.pi)⁻¹ * (1 + 1/(6*(m:ℝ)))) * (Real.sqrt 2 + 2*t^2) := by
      positivity
    exact mul_le_mul hstep1 hA3le hA3nn hstep1nn
  -- LOWER bound on A1*A2*A3
  have hLower : ((Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ)))) * Real.sqrt 2
        * (Real.exp (-(m:ℝ)*t^2/2) * (1 - (8/3)*(m:ℝ)*t^4)) ≤ A1*A2*A3 := by
    have hstep1 : ((Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ)))) * Real.sqrt 2 ≤ A1*A2 :=
      mul_le_mul hSRge hA2ge (Real.sqrt_nonneg 2) hA1nn
    have hstep1nn : (0:ℝ) ≤ ((Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ)))) * Real.sqrt 2 :=
      mul_nonneg hL1nn (Real.sqrt_nonneg 2)
    calc ((Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ)))) * Real.sqrt 2
          * (Real.exp (-(m:ℝ)*t^2/2) * (1 - (8/3)*(m:ℝ)*t^4))
        ≤ ((Real.sqrt Real.pi)⁻¹ * (1 - 2/(3*(m:ℝ)))) * Real.sqrt 2 * A3 :=
          mul_le_mul_of_nonneg_left hA3ge hstep1nn
      _ ≤ A1*A2*A3 := mul_le_mul_of_nonneg_right hstep1 hA3nn
  clear_value A1 A2 A3 t
  have hUdiff := region1_upper_diff m hm t
  have hLdiff := region1_lower_diff m hm t
  have hB := gaussianDensity_two_eq m hm t j htdef
  have hupper_final : A1*A2*A3 - Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)*t^2/2)
      ≤ ((Real.sqrt Real.pi)⁻¹ * (4*Real.exp (-1) + Real.sqrt 2/6 + 2*Real.exp (-1)/3)) / (m:ℝ) := by
    linarith [hUpper, hUdiff]
  have hlower_final : Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)*t^2/2) - A1*A2*A3
      ≤ (Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2/3 + 128*Real.exp (-2)/3)) / (m:ℝ) := by
    linarith [hLower, hLdiff]
  have hsplit : ((Real.sqrt Real.pi)⁻¹ * (4*Real.exp (-1) + Real.sqrt 2/6 + 2*Real.exp (-1)/3)) / (m:ℝ)
        + (Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2/3 + 128*Real.exp (-2)/3)) / (m:ℝ)
      = ((Real.sqrt Real.pi)⁻¹ * (4*Real.exp (-1) + Real.sqrt 2/6 + 2*Real.exp (-1)/3)
          + Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2/3 + 128*Real.exp (-2)/3)) / (m:ℝ) := by ring
  have hXnn : (0:ℝ) ≤ ((Real.sqrt Real.pi)⁻¹ * (4*Real.exp (-1) + Real.sqrt 2/6 + 2*Real.exp (-1)/3)) / (m:ℝ) := by
    positivity
  have hYnn : (0:ℝ) ≤ (Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2/3 + 128*Real.exp (-2)/3)) / (m:ℝ) := by
    positivity
  rw [heq, hB, abs_le]
  constructor
  · linarith [hlower_final, hsplit, hXnn]
  · linarith [hupper_final, hsplit, hYnn]



/-! ### Region 2: the far range `m/2 < |j| \le m-2`, and the extreme case `|j| = m` -/

theorem sqrt_le_self_of_one_le (m : ℝ) (hm : 1 ≤ m) : Real.sqrt m ≤ m := by
  nlinarith [Real.sq_sqrt (by linarith : (0:ℝ) ≤ m), Real.sqrt_nonneg m, sq_nonneg (Real.sqrt m - 1)]

theorem ab_facts_region2 (m : ℕ) (j : ℤ) (hj : j ≡ (m : ℤ) [ZMOD 2])
    (hjR2 : |(j:ℝ)| ≤ (m:ℝ) - 2) :
    1 ≤ (((m:ℤ)+j)/2).toNat ∧ 1 ≤ (((m:ℤ)-j)/2).toNat ∧
    (((m:ℤ)+j)/2).toNat + (((m:ℤ)-j)/2).toNat = m ∧
    (((((m:ℤ)+j)/2).toNat : ℤ)) - ((((m:ℤ)-j)/2).toNat : ℤ) = j := by
  have hjZ : |j| ≤ (m:ℤ) - 2 := by exact_mod_cast hjR2
  have hl : -|j| ≤ j := neg_abs_le j
  have hr : j ≤ |j| := le_abs_self j
  have hdvd2 : (2 : ℤ) ∣ ((m : ℤ) - j) := Int.ModEq.dvd hj
  have hdvd : (2 : ℤ) ∣ ((m : ℤ) + j) := by omega
  set a : ℕ := (((m:ℤ)+j)/2).toNat with ha
  set b : ℕ := (((m:ℤ)-j)/2).toNat with hb
  have hja : ((a:ℤ)) = ((m:ℤ)+j)/2 := by rw [ha]; exact Int.toNat_of_nonneg (by omega)
  have hjb : ((b:ℤ)) = ((m:ℤ)-j)/2 := by rw [hb]; exact Int.toNat_of_nonneg (by omega)
  have ha1 : 1 ≤ a := by
    have h : (1:ℤ) ≤ (a:ℤ) := by rw [hja]; omega
    exact_mod_cast h
  have hb1 : 1 ≤ b := by
    have h : (1:ℤ) ≤ (b:ℤ) := by rw [hjb]; omega
    exact_mod_cast h
  have hsum : a + b = m := by
    have h : (a:ℤ) + (b:ℤ) = (m:ℤ) := by rw [hja, hjb]; omega
    exact_mod_cast h
  have hdiff : ((a:ℤ)) - ((b:ℤ)) = j := by rw [hja, hjb]; omega
  exact ⟨ha1, hb1, hsum, hdiff⟩

theorem ab_ge_half_m (m a b : ℕ) (hab : a + b = m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (m:ℝ)/2 ≤ (a:ℝ) * (b:ℝ) := by
  rcases le_total a b with h | h
  · have hbm : (m:ℝ)/2 ≤ (b:ℝ) := by
      have hle : m ≤ 2*b := by omega
      have h2 : (m:ℝ) ≤ 2*(b:ℝ) := by exact_mod_cast hle
      linarith
    have ha1 : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
    have hbnn : (0:ℝ) ≤ (b:ℝ) := by positivity
    nlinarith [hbm, ha1, hbnn]
  · have ham : (m:ℝ)/2 ≤ (a:ℝ) := by
      have hle : m ≤ 2*a := by omega
      have h2 : (m:ℝ) ≤ 2*(a:ℝ) := by exact_mod_cast hle
      linarith
    have hb1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    have hann : (0:ℝ) ≤ (a:ℝ) := by positivity
    nlinarith [ham, hb1, hann]

theorem prefactor_le_sqrt_m (m a b : ℕ) (hm : 1 ≤ m) (hab : a + b = m) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (t : ℝ) (ht : (m:ℝ) * t = (a:ℝ) - (b:ℝ)) :
    Real.sqrt 2 / Real.sqrt (1 - t^2) ≤ Real.sqrt (m:ℝ) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have habR : (a:ℝ) + b = m := by exact_mod_cast hab
  have hquartic : (m:ℝ)^2 * (1 - t^2) = 4*(a:ℝ)*(b:ℝ) := by nlinarith [ht, habR]
  have hab2 : (m:ℝ)/2 ≤ (a:ℝ)*(b:ℝ) := ab_ge_half_m m a b hab ha hb
  have h1mt2 : (0:ℝ) < 1 - t^2 := by nlinarith [hquartic, hab2, hm0, sq_nonneg t]
  have hsqrt_eq : Real.sqrt (1 - t^2) = 2 * Real.sqrt ((a:ℝ)*(b:ℝ)) / (m:ℝ) := by
    have h1 : (1 - t^2) = 4*((a:ℝ)*(b:ℝ)) / (m:ℝ)^2 := by
      field_simp
      linarith [hquartic]
    rw [h1, Real.sqrt_div (by positivity) ((m:ℝ)^2), Real.sqrt_sq hm0.le,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
      show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsqrt_eq]
  have hsqrtab_pos : (0:ℝ) < Real.sqrt ((a:ℝ)*(b:ℝ)) := by
    apply Real.sqrt_pos.mpr
    nlinarith [hab2, hm0]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt ((a:ℝ)*(b:ℝ)) / (m:ℝ))]
  have hnn1 : (0:ℝ) ≤ Real.sqrt (m:ℝ) * (2 * Real.sqrt ((a:ℝ)*(b:ℝ)) / (m:ℝ)) := by positivity
  have hkey : (Real.sqrt 2)^2 ≤ (Real.sqrt (m:ℝ) * (2 * Real.sqrt ((a:ℝ)*(b:ℝ)) / (m:ℝ)))^2 := by
    have e1 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have e2 : (Real.sqrt (m:ℝ) * (2 * Real.sqrt ((a:ℝ)*(b:ℝ)) / (m:ℝ)))^2
        = (m:ℝ) * (4 * ((a:ℝ)*(b:ℝ)) / (m:ℝ)^2) := by
      rw [mul_pow, Real.sq_sqrt hm0.le, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (a:ℝ)*(b:ℝ))]
      ring
    rw [e1, e2]
    rw [show (m:ℝ) * (4 * ((a:ℝ)*(b:ℝ)) / (m:ℝ)^2) = 4*((a:ℝ)*(b:ℝ))/(m:ℝ) from by
      field_simp]
    rw [le_div_iff₀ hm0]
    linarith [hab2]
  nlinarith [hkey, hnn1, Real.sqrt_nonneg (2:ℝ)]

/-- **The region-2 (far range) bound.** -/
theorem region2_bound (m : ℕ) (hm : 1 ≤ m) (j : ℤ) (hj : j ≡ (m:ℤ) [ZMOD 2])
    (hjR1 : (m:ℝ)/2 < |(j:ℝ)|) (hjR2 : |(j:ℝ)| ≤ (m:ℝ) - 2) :
    |Real.sqrt m * binomPMF m j - 2 * gaussianDensity ((j:ℝ)/Real.sqrt m)|
      ≤ (((Real.sqrt Real.pi)⁻¹ * (7/6)) * (256*Real.exp (-2))
          + Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (8*Real.exp (-1))) / (m:ℝ) := by
  obtain ⟨ha1, hb1, hab, hdiff⟩ := ab_facts_region2 m j hj hjR2
  set a := (((m:ℤ)+j)/2).toNat with ha_def
  set b := (((m:ℤ)-j)/2).toNat with hb_def
  have heq := sqrt_mul_binomPMF_eq m hm j hj (by exact_mod_cast hjR2)
  set t := (j:ℝ)/(m:ℝ) with htdef
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have htabs : 1/2 < |t| := by
    rw [htdef, abs_div, abs_of_pos hm0, lt_div_iff₀ hm0]
    linarith [hjR1]
  have htabs1 : |t| < 1 := by
    rw [htdef, abs_div, abs_of_pos hm0, div_lt_one hm0]
    linarith [hjR2]
  have ht2gt : (1:ℝ)/4 < t^2 := by nlinarith [htabs, abs_nonneg t, sq_abs t]
  set A1 := Stirling.stirlingSeq m
      / (Stirling.stirlingSeq (((m:ℤ)+j)/2).toNat * Stirling.stirlingSeq (((m:ℤ)-j)/2).toNat)
    with hA1def
  set A2 := Real.sqrt 2 / Real.sqrt (1 - t^2) with hA2def
  set A3 := Real.exp (-(m:ℝ) * gfun t) with hA3def
  have hSRle : A1 ≤ (Real.sqrt Real.pi)⁻¹ * (1 + 1/(6*(m:ℝ))) :=
    stirling_ratio_upper_m m _ _ hab ha1 hb1 hm
  have hSRle2 : A1 ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) := by
    have hstep : (1:ℝ)/(6*(m:ℝ)) ≤ 1/6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hm1]
    have hone : (1:ℝ) + 1/(6*(m:ℝ)) ≤ 7/6 := by linarith [hstep]
    calc A1 ≤ (Real.sqrt Real.pi)⁻¹ * (1+1/(6*(m:ℝ))) := hSRle
      _ ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) := by
        apply mul_le_mul_of_nonneg_left hone (by positivity)
  have htaeq : (m:ℝ) * t = (a:ℝ) - (b:ℝ) := by
    have h1 : (m:ℝ) * t = (j:ℝ) := by rw [htdef]; field_simp
    rw [h1]
    have h2 : ((a:ℤ):ℝ) - ((b:ℤ):ℝ) = (j:ℝ) := by exact_mod_cast hdiff
    push_cast at h2
    linarith [h2]
  have hA2 := ab_ge_half_m m a b hab ha1 hb1
  have hA2le : A2 ≤ Real.sqrt (m:ℝ) := prefactor_le_sqrt_m m a b hm hab ha1 hb1 t htaeq
  have hA2nn : (0:ℝ) ≤ A2 := by rw [hA2def]; positivity
  have hA3le : A3 ≤ Real.exp (-(m:ℝ)/8) := by
    have hgfun := gfun_ge_half_sq t htabs1
    rw [hA3def]
    apply Real.exp_le_exp.mpr
    nlinarith [hgfun, ht2gt, hm0.le]
  have hA3nn : (0:ℝ) ≤ A3 := by rw [hA3def]; positivity
  have hA1nn : (0:ℝ) ≤ A1 := by
    rw [hA1def]
    have hSmpos : (0:ℝ) < Stirling.stirlingSeq m := by
      have hspm := Stirling.sqrt_pi_le_stirlingSeq (n := m) (by omega)
      have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      linarith
    have hSapos : (0:ℝ) < Stirling.stirlingSeq a := by
      have hspa := Stirling.sqrt_pi_le_stirlingSeq (n := a) (by omega)
      have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      linarith
    have hSbpos : (0:ℝ) < Stirling.stirlingSeq b := by
      have hspb := Stirling.sqrt_pi_le_stirlingSeq (n := b) (by omega)
      have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      linarith
    positivity
  have hP_le : Real.sqrt m * binomPMF m j ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) * Real.sqrt (m:ℝ)
      * Real.exp (-(m:ℝ)/8) := by
    rw [heq]
    have step1 : A1 * A2 ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) * Real.sqrt (m:ℝ) :=
      mul_le_mul hSRle2 hA2le hA2nn (by positivity)
    have step1nn : (0:ℝ) ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) * Real.sqrt (m:ℝ) := by positivity
    exact mul_le_mul step1 hA3le hA3nn step1nn
  have hsqrtm_le_m : Real.sqrt (m:ℝ) ≤ (m:ℝ) := sqrt_le_self_of_one_le (m:ℝ) hm1
  have hexp_pos : (0:ℝ) < Real.exp (-(m:ℝ)/8) := Real.exp_pos _
  have hm2exp : (m:ℝ)^2 * Real.exp (-((1/8:ℝ)*(m:ℝ))) ≤ 4*Real.exp (-2)/(1/8:ℝ)^2 :=
    sq_linear_exp_bound (1/8) (m:ℝ) (by norm_num) hm0.le
  have hm2exp' : (m:ℝ)^2 * Real.exp (-(m:ℝ)/8) ≤ 256*Real.exp (-2) := by
    have heqexp : -((1/8:ℝ)*(m:ℝ)) = -(m:ℝ)/8 := by ring
    rw [heqexp] at hm2exp
    have heqconst : (4:ℝ)*Real.exp (-2)/(1/8:ℝ)^2 = 256*Real.exp (-2) := by ring
    linarith [hm2exp, heqconst.le, heqconst.ge]
  have hsqrtm_exp : Real.sqrt (m:ℝ) * Real.exp (-(m:ℝ)/8) ≤ 256*Real.exp (-2)/(m:ℝ) := by
    have h1 : Real.sqrt (m:ℝ) * Real.exp (-(m:ℝ)/8) ≤ (m:ℝ) * Real.exp (-(m:ℝ)/8) :=
      mul_le_mul_of_nonneg_right hsqrtm_le_m hexp_pos.le
    have h2 : (m:ℝ) * Real.exp (-(m:ℝ)/8) ≤ 256*Real.exp (-2)/(m:ℝ) := by
      rw [le_div_iff₀ hm0]
      calc (m:ℝ) * Real.exp (-(m:ℝ)/8) * (m:ℝ) = (m:ℝ)^2 * Real.exp (-(m:ℝ)/8) := by ring
        _ ≤ 256*Real.exp (-2) := hm2exp'
    linarith [h1, h2]
  have hP_final : Real.sqrt m * binomPMF m j
      ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) * (256*Real.exp (-2)) / (m:ℝ) := by
    calc Real.sqrt m * binomPMF m j
        ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) * Real.sqrt (m:ℝ) * Real.exp (-(m:ℝ)/8) := hP_le
      _ = (Real.sqrt Real.pi)⁻¹ * (7/6) * (Real.sqrt (m:ℝ) * Real.exp (-(m:ℝ)/8)) := by ring
      _ ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) * (256*Real.exp (-2)/(m:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hsqrtm_exp (by positivity)
      _ = (Real.sqrt Real.pi)⁻¹ * (7/6) * (256*Real.exp (-2)) / (m:ℝ) := by ring
  have hB := gaussianDensity_two_eq m hm t j htdef
  have hgd_le : 2*gaussianDensity ((j:ℝ)/Real.sqrt m)
      ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (8*Real.exp (-1)) / (m:ℝ) := by
    rw [hB]
    have hexple : Real.exp (-(m:ℝ)*t^2/2) ≤ Real.exp (-(m:ℝ)/8) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ht2gt, hm0.le]
    have hme : (m:ℝ) * Real.exp (-((1/8:ℝ)*(m:ℝ))) ≤ Real.exp (-1)/(1/8:ℝ) :=
      linear_exp_bound (1/8) (m:ℝ) (by norm_num)
    have hme' : (m:ℝ) * Real.exp (-(m:ℝ)/8) ≤ 8*Real.exp (-1) := by
      have heqexp : -((1/8:ℝ)*(m:ℝ)) = -(m:ℝ)/8 := by ring
      rw [heqexp] at hme
      have heqconst : Real.exp (-1:ℝ)/(1/8:ℝ) = 8*Real.exp (-1) := by ring
      linarith [hme, heqconst.le, heqconst.ge]
    have hexp_le_div : Real.exp (-(m:ℝ)/8) ≤ 8*Real.exp (-1)/(m:ℝ) := by
      rw [le_div_iff₀ hm0]
      linarith [hme']
    calc Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)*t^2/2)
        ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)/8) := by
          apply mul_le_mul_of_nonneg_left hexple (by positivity)
      _ ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (8*Real.exp (-1)/(m:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hexp_le_div (by positivity)
      _ = Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (8*Real.exp (-1)) / (m:ℝ) := by ring
  have hgd_nn : (0:ℝ) ≤ 2*gaussianDensity ((j:ℝ)/Real.sqrt m) := by
    rw [hB]; positivity
  have hP_nn : (0:ℝ) ≤ Real.sqrt m * binomPMF m j := by
    rw [heq]; positivity
  have hXnn : (0:ℝ) ≤ (Real.sqrt Real.pi)⁻¹ * (7/6) * (256*Real.exp (-2)) / (m:ℝ) := by positivity
  have hYnn : (0:ℝ) ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (8*Real.exp (-1)) / (m:ℝ) := by positivity
  have hsplit : (Real.sqrt Real.pi)⁻¹ * (7/6) * (256*Real.exp (-2)) / (m:ℝ)
        + Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (8*Real.exp (-1)) / (m:ℝ)
      = (((Real.sqrt Real.pi)⁻¹ * (7/6)) * (256*Real.exp (-2))
          + Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (8*Real.exp (-1))) / (m:ℝ) := by ring
  rw [abs_le]
  constructor
  · linarith [hgd_le, hP_nn, hXnn, hsplit]
  · linarith [hP_final, hgd_nn, hYnn, hsplit]

/-- **The extreme case `|j| = m`.** -/
theorem binomPMF_extreme (m : ℕ) (j : ℤ) (hjeq : |j| = (m:ℤ)) :
    binomPMF m j = 1 / 2^m := by
  rcases abs_eq (by positivity : (0:ℤ) ≤ (m:ℤ)) |>.mp hjeq with h | h
  · have hval : (((m:ℤ)+j)/2).toNat = m := by omega
    rw [binomPMF, hval, Nat.choose_self]
    norm_num
  · have hval : (((m:ℤ)+j)/2).toNat = 0 := by omega
    rw [binomPMF, hval, Nat.choose_zero_right]
    norm_num

theorem extreme_bound (m : ℕ) (hm : 1 ≤ m) (j : ℤ) (hjeq : |(j:ℝ)| = (m:ℝ)) :
    |Real.sqrt m * binomPMF m j - 2 * gaussianDensity ((j:ℝ)/Real.sqrt m)|
      ≤ (4*Real.exp (-2)/(Real.log 2)^2
          + Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2*Real.exp (-1))) / (m:ℝ) := by
  have hjeqZ : |j| = (m:ℤ) := by exact_mod_cast hjeq
  have hbin := binomPMF_extreme m j hjeqZ
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2m : (2:ℝ)^m = Real.exp ((m:ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hbound1 : Real.sqrt m * binomPMF m j ≤ (4*Real.exp (-2)/(Real.log 2)^2) / (m:ℝ) := by
    rw [hbin, h2m]
    have heq1 : Real.sqrt (m:ℝ) * (1/Real.exp ((m:ℝ)*Real.log 2))
        = Real.sqrt (m:ℝ) * Real.exp (-(Real.log 2 * (m:ℝ))) := by
      rw [Real.exp_neg]
      congr 2
      ring
    rw [heq1]
    have hsqrtm_le_m : Real.sqrt (m:ℝ) ≤ (m:ℝ) := sqrt_le_self_of_one_le (m:ℝ) hm1
    have hexp_pos : (0:ℝ) < Real.exp (-(Real.log 2 * (m:ℝ))) := Real.exp_pos _
    have h1 : Real.sqrt (m:ℝ) * Real.exp (-(Real.log 2 * (m:ℝ)))
        ≤ (m:ℝ) * Real.exp (-(Real.log 2 * (m:ℝ))) :=
      mul_le_mul_of_nonneg_right hsqrtm_le_m hexp_pos.le
    have hkey := sq_linear_exp_bound (Real.log 2) (m:ℝ) hlog2pos hm0.le
    have h2 : (m:ℝ) * Real.exp (-(Real.log 2 * (m:ℝ))) ≤ (4*Real.exp (-2)/(Real.log 2)^2) / (m:ℝ) := by
      rw [le_div_iff₀ hm0]
      calc (m:ℝ) * Real.exp (-(Real.log 2 * (m:ℝ))) * (m:ℝ)
            = (m:ℝ)^2 * Real.exp (-(Real.log 2 * (m:ℝ))) := by ring
        _ ≤ 4*Real.exp (-2)/(Real.log 2)^2 := hkey
    linarith [h1, h2]
  have ht2eq : (j:ℝ)/(m:ℝ) = 1 ∨ (j:ℝ)/(m:ℝ) = -1 := by
    rcases abs_eq hm0.le |>.mp hjeq with h | h
    · left; rw [h]; field_simp
    · right; rw [h]; field_simp
  have ht2sq : ((j:ℝ)/(m:ℝ))^2 = 1 := by
    rcases ht2eq with h | h <;> rw [h] <;> ring
  have hB := gaussianDensity_two_eq m hm ((j:ℝ)/(m:ℝ)) j rfl
  have hme : (m:ℝ) * Real.exp (-((1/2:ℝ)*(m:ℝ))) ≤ Real.exp (-1)/(1/2:ℝ) :=
    linear_exp_bound (1/2) (m:ℝ) (by norm_num)
  have heq2 : -((1/2:ℝ)*(m:ℝ)) = -(m:ℝ)/2 := by ring
  rw [heq2] at hme
  have heqc : Real.exp (-1:ℝ)/(1/2:ℝ) = 2*Real.exp (-1) := by ring
  rw [heqc] at hme
  have hexple : (m:ℝ) * Real.exp (-(m:ℝ)/2) ≤ 2*Real.exp (-1) := hme
  have hstep : Real.exp (-(m:ℝ)/2) ≤ 2*Real.exp (-1)/(m:ℝ) := by
    rw [le_div_iff₀ hm0]; linarith [hexple]
  have hgd_le : 2*gaussianDensity ((j:ℝ)/Real.sqrt m)
      ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2*Real.exp (-1)) / (m:ℝ) := by
    rw [hB]
    have heqexp : -(m:ℝ) * ((j:ℝ)/(m:ℝ))^2 / 2 = -(m:ℝ)/2 := by rw [ht2sq]; ring
    rw [heqexp]
    have hconst_nn : (0:ℝ) ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ := by positivity
    calc Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * Real.exp (-(m:ℝ)/2)
        ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2*Real.exp (-1)/(m:ℝ)) :=
          mul_le_mul_of_nonneg_left hstep hconst_nn
      _ = Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2*Real.exp (-1)) / (m:ℝ) := by ring
  have hP_nn : (0:ℝ) ≤ Real.sqrt m * binomPMF m j := by rw [hbin]; positivity
  have hgd_nn : (0:ℝ) ≤ 2*gaussianDensity ((j:ℝ)/Real.sqrt m) := by rw [hB]; positivity
  have hXnn : (0:ℝ) ≤ 4*Real.exp (-2)/(Real.log 2)^2 / (m:ℝ) := by positivity
  have hYnn : (0:ℝ) ≤ Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2*Real.exp (-1)) / (m:ℝ) := by positivity
  have hsplit : 4*Real.exp (-2)/(Real.log 2)^2 / (m:ℝ)
        + Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2*Real.exp (-1)) / (m:ℝ)
      = (4*Real.exp (-2)/(Real.log 2)^2
          + Real.sqrt 2 * (Real.sqrt Real.pi)⁻¹ * (2*Real.exp (-1))) / (m:ℝ) := by ring
  rw [abs_le]
  constructor
  · linarith [hgd_le, hP_nn, hXnn, hsplit]
  · linarith [hbound1, hgd_nn, hYnn, hsplit]

end LatticeProb.BinomialLCLT

end

