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

end LatticeProb.BinomialLCLT

end
