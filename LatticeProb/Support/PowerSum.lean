/-
Sums of a real power over an initial segment of the integers, bounded by the
matching power of the length.

This is the elementary estimate behind the near-diagonal bound of the
Green-function estimates in dimensions below four: the double time sum of
transition probabilities over a microscopic time window is compared with a
product of two such power sums, one in each time variable, and the two exponents
are chosen so that the two lengths enter with the powers that the prefactor
cancels exactly.

The bound comes from Bernoulli's inequality for exponents in the unit interval:
for `0 < β ≤ 1` and `x ≥ 1`,

  `β x^{β-1} ≤ x^β - (x-1)^β`,

since `(x-1)^β = x^β (1 - 1/x)^β ≤ x^β (1 - β/x)`.  Summing this over
`x = 1, …, N` telescopes to `N^β`.
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section

namespace LatticeProb.PowerSum

/-- One step of the telescoping estimate: for an exponent in the unit interval the
increment of `x ↦ x^β` over a unit step to the left dominates `β` times the
derivative read at the right endpoint.  This is Bernoulli's inequality. -/
theorem rpow_step_le {β x : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hx : 1 ≤ x) :
    β * x ^ (β - 1) ≤ x ^ β - (x - 1) ^ β := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
  have hu : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  have hu0 : (0:ℝ) < 1 / x := by positivity
  have hs : (-1 : ℝ) ≤ -(1/x) := by linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hβ0.le hβ1
  have hfac : x - 1 = x * (1 + -(1/x)) := by field_simp; ring
  have hnn : (0:ℝ) ≤ 1 + -(1/x) := by linarith
  have hxb : (0:ℝ) < x ^ β := Real.rpow_pos_of_pos hx0 β
  have hmul : (x - 1) ^ β = x ^ β * (1 + -(1/x)) ^ β := by
    rw [hfac, Real.mul_rpow hx0.le hnn]
  have hd : x ^ (β - 1) = x ^ β / x := by
    rw [Real.rpow_sub hx0, Real.rpow_one]
  rw [hmul, hd]
  have h1 : x ^ β * (1 + -(1/x)) ^ β ≤ x ^ β * (1 + β * -(1/x)) :=
    mul_le_mul_of_nonneg_left hb hxb.le
  have h2 : x ^ β * (1 + β * -(1/x)) = x ^ β - β * (x ^ β / x) := by
    field_simp
    ring
  linarith [h1, h2]

/-- **The sum of `j^{β-1}` over `j = 1, …, N` is at most `N^β/β`**, for an exponent
`β` in the unit interval.  The two instances used below are `β = 1 - γ` and
`β = 1 - (d/2 - γ)`, with `γ` the splitting exponent of the two time variables. -/
theorem sum_succ_rpow_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ (β - 1) ≤ (N : ℝ) ^ β / β := by
  rw [le_div_iff₀ hβ0, Finset.sum_mul]
  have hstep : ∀ j ∈ Finset.range N, ((j : ℝ) + 1) ^ (β - 1) * β
      ≤ (((j : ℕ) + 1 : ℕ) : ℝ) ^ β - ((j : ℕ) : ℝ) ^ β := by
    intro j _
    have hx : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have h := rpow_step_le hβ0 hβ1 hx
    have hc : (((j : ℕ) + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hc]
    have hc2 : ((j : ℝ) + 1) - 1 = (j : ℝ) := by ring
    rw [hc2] at h
    linarith
  refine le_trans (Finset.sum_le_sum hstep) ?_
  have htel := Finset.sum_range_sub (f := fun n : ℕ => ((n : ℕ) : ℝ) ^ β) N
  rw [htel]
  have hz : ((0 : ℕ) : ℝ) ^ β = 0 := by
    rw [Nat.cast_zero]
    exact Real.zero_rpow (ne_of_gt hβ0)
  rw [hz, sub_zero]

end LatticeProb.PowerSum
