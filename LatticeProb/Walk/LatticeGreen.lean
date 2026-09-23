import LatticeProb.Walk.LocalCLT
import LatticeProb.Walk.SRW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

/-- The finite-time Green kernel `g_t(x, y) = ∑_{k<t} p_k(x, y)`. -/
noncomputable def greenTime (d : ℕ) (t : ℕ) (x y : Site d) : ℝ :=
  ∑ k ∈ Finset.range t, LocalCLT.heatKernel d k x y

/-- The two-point kernel and the one-point kernel have the same recursion, so they
agree through the difference of the two sites. -/
theorem heatKernel_eq_srwHeat (d : ℕ) :
    ∀ (k : ℕ) (x y : Site d),
      LocalCLT.heatKernel d k x y = srwHeat d k (x - y) := by
  intro k
  induction k with
  | zero =>
      intro x y
      show (if x = y then (1 : ℝ) else 0) = if x - y = 0 then 1 else 0
      by_cases h : x = y
      · simp [h]
      · have : x - y ≠ 0 := fun hc => h (by rwa [sub_eq_zero] at hc)
        simp [h, this]
  | succ j ih =>
      intro x y
      show (∑ i : Fin d, (LocalCLT.heatKernel d j (x + unit i) y
              + LocalCLT.heatKernel d j (x - unit i) y)) / (2 * d)
          = walkOp (srwHeat d j) (x - y)
      unfold walkOp nbrSum
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih (x + unit i) y, ih (x - unit i) y]
      congr 2 <;> abel

/-- The two-point Green kernel is the one-point Green kernel at the difference
of the two sites. -/
theorem greenTime_eq_srwGreen (d t : ℕ) (x y : Site d) :
    greenTime d t x y = srwGreen d t (x - y) := by
  rw [greenTime, srwGreen]
  exact Finset.sum_congr rfl fun k _ => heatKernel_eq_srwHeat d k x y

/-- The Green kernel from the origin, in the one-point form.  The argument is
`-y` because the identification is through `x - y`. -/
theorem greenTime_origin_eq_srwGreen_neg (d t : ℕ) (y : Site d) :
    greenTime d t 0 y = srwGreen d t (-y) := by
  simpa using greenTime_eq_srwGreen d t 0 y

end LatticeProb
