/-
The on-diagonal sup bound for the simple random walk kernel on `ℤ^d`.

The schedule decomposition of `LatticeProb/Walk/SRWDecomp.lean` writes the
`r`-step simple kernel as the average over coordinate schedules of a product of
one-dimensional kernels, and `LatticeProb/Walk/SRWOneDim.lean` bounds each such
factor by `√2 / √(n+1)`.  Feeding those two facts into the multinomial Chernoff
estimate already used for the lazy walk in `LatticeProb/Walk/GreenBounds.lean`
gives `srwHeat d R x ≤ √2^d · C_d · R^{-d/2}`, the simple-walk counterpart of
`LatticeProb.iterate_delta0_sup_bound`.  The only difference from the lazy
statement is the constant `√2^d`, one factor of `√2` per coordinate coming from
the parity of the one-dimensional walk.
-/
import Mathlib
import LatticeProb.Walk.SRWDecomp
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.GreenBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- The product kernel of a schedule is bounded by the corresponding product of
one-dimensional peaks, at the cost of one factor `√2` per coordinate. -/
lemma KS_le_prod (n : Fin d → ℕ) (x : Site d) :
    KS n x ≤ Real.sqrt 2 ^ d * ∏ i, (1 : ℝ) / Real.sqrt ((n i : ℝ) + 1) := by
  have hterm : KS n x ≤ ∏ i : Fin d, Real.sqrt 2 / Real.sqrt ((n i : ℝ) + 1) := by
    unfold KS
    exact Finset.prod_le_prod (fun i _ => S1_nonneg (n i) (x i))
      (fun i _ => srwHeat_one_le (n i) (x i))
  refine le_trans hterm (le_of_eq ?_)
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const,
    Finset.prod_const_one, Finset.card_univ, Fintype.card_fin]
  ring

/-- The schedule bound for the simple walk: the `r`-step kernel is at most
`√2^d` times the schedule average of `∏_i (N_i+1)^{-1/2}`. -/
lemma srwHeat_le_sched (hd : 0 < d) (r : ℕ) (x : Site d) :
    srwHeat d r x
      ≤ Real.sqrt 2 ^ d
        * (∑ c : Fin r → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) / (d : ℝ) ^ r := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdpow : (0 : ℝ) < (d : ℝ) ^ r := by positivity
  rw [srwHeat_eq_sched hd r x, div_le_div_iff_of_pos_right hdpow, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => KS_le_prod (cnt c) x

/-- `‖P^R(0, ·)‖_∞ ≤ √2^d · C_d · R^{-d/2}` for the simple random walk. -/
theorem srwHeat_sup_bound (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (x : Site d) :
    srwHeat d R x ≤ Real.sqrt 2 ^ d * greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdRpow : (0 : ℝ) < (d : ℝ) ^ R := by positivity
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 ^ d := by positivity
  have hSAB : (∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) / (d : ℝ) ^ R
      ≤ ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
        + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ))) := by
    rw [div_le_iff₀ hdRpow]
    calc ∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
        ≤ _ := sched_sum_bound (d := d) hd R
      _ = (((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
            + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) * (d : ℝ) ^ R := by ring
  have hAB : ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
      + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))
      ≤ greenConst d * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
    rw [greenConst, add_mul]
    linarith [bulk_le (d := d) hd hR, tail_le (d := d) hd hR]
  calc srwHeat d R x
      ≤ Real.sqrt 2 ^ d
        * (∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1))
          / (d : ℝ) ^ R := srwHeat_le_sched hd R x
    _ = Real.sqrt 2 ^ d
        * ((∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1))
          / (d : ℝ) ^ R) := mul_div_assoc _ _ _
    _ ≤ Real.sqrt 2 ^ d * (((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
          + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) :=
        mul_le_mul_of_nonneg_left hSAB hs2
    _ ≤ Real.sqrt 2 ^ d * (greenConst d * ((Real.sqrt (R : ℝ)) ^ d)⁻¹) :=
        mul_le_mul_of_nonneg_left hAB hs2
    _ = Real.sqrt 2 ^ d * greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2) := by
        rw [rpow_neg_half_eq d R]; ring

end LatticeProb
