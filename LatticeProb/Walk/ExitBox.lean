/-
The exit time of a box.

`LatticeProb.u_bound` bounds the mean exit time of an arbitrary finite set `A`
by `C |A|^{2/d}`.  A box of radius `r` has `(2r+1)^d` sites, so its mean exit
time is at most `C (2r+1)^2`, uniformly in the starting site and in the
dimension, and the total mass of the mean exit time over the box is at most
`C (2r+1)^{d+2}`.  These are the forms in which the estimate is used: the exit
time of a box of radius `r` is of order `r^2`.
-/
import LatticeProb.Walk.ExitTime
import LatticeProb.Walk.RangeBox

namespace LatticeProb

open Finset

variable {d : ℕ}

/-- The number of sites in the box of radius `r`. -/
theorem card_originBox' (r : ℕ) : (originBox d r).card = (2 * r + 1) ^ d :=
  card_originBox r

/-- `((2r+1)^d)^{2/d} = (2r+1)^2` for `d ≥ 1`. -/
theorem rpow_card_originBox (hd : 0 < d) (r : ℕ) :
    ((((2 * r + 1) ^ d : ℕ) : ℝ)) ^ ((2 : ℝ) / (d : ℝ)) = ((2 * r + 1 : ℕ) : ℝ) ^ 2 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  rw [Nat.cast_pow, ← Real.rpow_natCast (((2 * r + 1 : ℕ) : ℝ)) d,
    ← Real.rpow_mul hm.le]
  rw [show (d : ℝ) * ((2 : ℝ) / (d : ℝ)) = 2 by field_simp]
  rw [Real.rpow_two]

/-- The mean exit time of the box of radius `r` is at most `C (2r+1)^2`,
uniformly in the starting site. -/
theorem u_originBox_le (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (x : Site d),
      u (originBox d r) x ≤ C * ((2 * r + 1 : ℕ) : ℝ) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := u_bound hd
  refine ⟨C, hCpos, fun r x => ?_⟩
  have h := hC (originBox d r) x
  rwa [card_originBox' r, rpow_card_originBox hd r] at h

/-- The total mass of the mean exit time of the box of radius `r` is at most
`C (2r+1)^{d+2}`. -/
theorem T_originBox_le (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      T (originBox d r) ≤ C * ((2 * r + 1 : ℕ) : ℝ) ^ (d + 2) := by
  obtain ⟨C, hCpos, hC⟩ := u_originBox_le hd
  refine ⟨C, hCpos, fun r => ?_⟩
  have hsum : T (originBox d r) ≤ ∑ _x ∈ originBox d r, C * ((2 * r + 1 : ℕ) : ℝ) ^ 2 := by
    rw [T]
    exact Finset.sum_le_sum fun x _ => hC r x
  rw [Finset.sum_const, card_originBox' r, nsmul_eq_mul] at hsum
  refine hsum.trans (le_of_eq ?_)
  push_cast
  ring

end LatticeProb
