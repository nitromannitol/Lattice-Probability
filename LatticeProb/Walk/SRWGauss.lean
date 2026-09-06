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

end LatticeProb
