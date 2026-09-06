/-
Two elementary ingredients of the Gaussian bound on the lattice kernel.

The first is that a schedule of `r` coordinate choices distributes exactly `r`
steps among the coordinates.  The second is Sedrakyan's form of the Cauchy
inequality, which turns a product of one-dimensional Gaussian factors, one for
each coordinate and each with its own number of steps, into a single Gaussian
factor in the `ℓ¹` norm of the site and the total number of steps.
-/
import Mathlib
import LatticeProb.Walk.SRW
import LatticeProb.Walk.Decomp
import LatticeProb.Walk.GreenBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- A schedule of length `r` distributes exactly `r` steps among the coordinates. -/
theorem sum_cnt {r : ℕ} (c : Fin r → Fin d) : ∑ i, cnt c i = r := by
  classical
  simp only [cnt]
  rw [Finset.sum_comm]
  have : ∀ t : Fin r, ∑ i : Fin d, (if c t = i then 1 else 0) = 1 := by
    intro t
    rw [Finset.sum_ite_eq Finset.univ (c t) (fun _ => (1 : ℕ))]
    simp
  rw [Finset.sum_congr rfl fun t _ => this t]
  simp

/-- Sedrakyan's inequality applied to the coordinates of a site: the sum of the
one-dimensional Gaussian exponents is at least the `ℓ¹` exponent. -/
theorem graphNorm_sq_div_le (x : Site d) (N : Fin d → ℕ) :
    ((graphNorm x : ℝ)) ^ 2 / (∑ i, ((N i : ℝ) + 1))
      ≤ ∑ i, ((x i : ℝ)) ^ 2 / ((N i : ℝ) + 1) := by
  have hg : ∀ i ∈ (univ : Finset (Fin d)), (0 : ℝ) < (N i : ℝ) + 1 := by
    intro i _; positivity
  have h := Finset.sq_sum_div_le_sum_sq_div (univ : Finset (Fin d))
    (fun i => |((x i : ℝ))|) hg
  have hsum : ∑ i, |((x i : ℝ))| = (graphNorm x : ℝ) := by
    rw [graphNorm]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hsq : ∀ i : Fin d, |((x i : ℝ))| ^ 2 = ((x i : ℝ)) ^ 2 := fun i => sq_abs _
  rw [hsum] at h
  refine h.trans_eq ?_
  exact Finset.sum_congr rfl fun i _ => by rw [hsq i]

/-- Sedrakyan's inequality for the coordinates of a site against arbitrary
positive weights. -/
theorem graphNorm_sq_div_le_of_pos (x : Site d) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) :
    ((graphNorm x : ℝ)) ^ 2 / (∑ i, w i) ≤ ∑ i, ((x i : ℝ)) ^ 2 / w i := by
  have hg : ∀ i ∈ (univ : Finset (Fin d)), (0 : ℝ) < w i := fun i _ => hw i
  have h := Finset.sq_sum_div_le_sum_sq_div (univ : Finset (Fin d))
    (fun i => |((x i : ℝ))|) hg
  have hsum : ∑ i, |((x i : ℝ))| = (graphNorm x : ℝ) := by
    rw [graphNorm]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hsum] at h
  refine h.trans_eq ?_
  exact Finset.sum_congr rfl fun i _ => by rw [sq_abs]

/-- The product over the coordinates of the one-dimensional Gaussian factors is
at most a single Gaussian factor in the `ℓ¹` norm and the total weight. -/
theorem prod_exp_le (x : Site d) (n : Fin d → ℕ) :
    ∏ i, Real.exp (-((x i : ℝ)) ^ 2 / (8 * ((n i : ℝ) + 2)))
      ≤ Real.exp (-((graphNorm x : ℝ)) ^ 2 / (8 * (∑ i, ((n i : ℝ) + 2)))) := by
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  have hw : ∀ i : Fin d, (0 : ℝ) < 8 * ((n i : ℝ) + 2) := by
    intro i; positivity
  have h := graphNorm_sq_div_le_of_pos x (fun i => 8 * ((n i : ℝ) + 2)) hw
  have hsum : ∑ i, (8 * ((n i : ℝ) + 2)) = 8 * (∑ i, ((n i : ℝ) + 2)) := by
    rw [Finset.mul_sum]
  rw [hsum] at h
  have hrw : ∀ i : Fin d,
      -((x i : ℝ)) ^ 2 / (8 * ((n i : ℝ) + 2)) = -(((x i : ℝ)) ^ 2 / (8 * ((n i : ℝ) + 2))) := by
    intro i; ring
  rw [Finset.sum_congr rfl fun i _ => hrw i, Finset.sum_neg_distrib]
  have hgn : -((graphNorm x : ℝ)) ^ 2 / (8 * (∑ i, ((n i : ℝ) + 2)))
      = -(((graphNorm x : ℝ)) ^ 2 / (8 * (∑ i, ((n i : ℝ) + 2)))) := by ring
  rw [hgn]
  exact neg_le_neg h

/-- The total weight attached to a schedule of length `r`. -/
theorem sum_cnt_add_two {r : ℕ} (c : Fin r → Fin d) :
    ∑ i, ((cnt c i : ℝ) + 2) = (r : ℝ) + 2 * d := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i, ((cnt c i : ℕ) : ℝ) = (r : ℝ) := by
    rw [← Nat.cast_sum, sum_cnt]
  rw [h1]
  simp [Finset.sum_const, mul_comm]

/-- The schedule average of `∏_i (N_i+1)^{-1/2}` is of order `R^{-d/2}`.  This
is the analytic core of every sup bound on an `R`-step kernel; it does not
mention the walk. -/
theorem sched_avg_le (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) :
    (∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) / (d : ℝ) ^ R
      ≤ greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdRpow : (0 : ℝ) < (d : ℝ) ^ R := by positivity
  have h2 := sched_sum_bound (d := d) hd R
  have h3 : (∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) / (d : ℝ) ^ R
      ≤ ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
        + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ))) := by
    rw [div_le_iff₀ hdRpow]
    calc ∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
        ≤ _ := h2
      _ = (((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
            + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) * (d : ℝ) ^ R := by ring
  rw [rpow_neg_half_eq d R, greenConst, add_mul]
  linarith [h3, bulk_le (d := d) hd hR, tail_le (d := d) hd hR]

end LatticeProb
