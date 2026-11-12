import LatticeProb.LQG.InternalMetricDyadicSmallCells

/-!
# The level-`K` cell of a square containing the origin at a corner

Let `S = [a, a + s] × [b, b + s]` with `s > 0` and `a, b ∈ {0, -s}`, so that the origin is a corner of `S`.
If the closed dyadic subsquare of `S` of level `K` with indices `(I, J)` (both `< 2 ^ K`) contains the origin,
then it is the corner cell: `I = 0` when `a = 0` and `I = 2 ^ K - 1` when `a = -s`, and likewise for `J`.

## Main statement

* `LatticeProb.LQG.eq_cornerIndex_of_zero_mem_closedDyadicSubsquare`.
-/

open Set

namespace LatticeProb.LQG

/-- One coordinate of the corner-cell statement: if the origin lies in the interval
`[a + I s 2⁻ᴷ, a + I s 2⁻ᴷ + s 2⁻ᴷ]` with `a ∈ {0, -s}` and `I < 2 ^ K`, then `I = 0` for `a = 0` and
`I = 2 ^ K - 1` for `a = -s`. -/
theorem eq_cornerIndex_of_zero_mem_Icc {a s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) {K I : ℕ}
    (hI : I < 2 ^ K)
    (h : (0 : ℝ) ∈ Icc (a + I * (s / 2 ^ K)) (a + I * (s / 2 ^ K) + s / 2 ^ K)) :
    I = if a = 0 then 0 else 2 ^ K - 1 := by
  have hpos : (0 : ℝ) < s / 2 ^ K := by positivity
  have hsK : (2 : ℝ) ^ K * (s / 2 ^ K) = s := by field_simp
  obtain ⟨h1, h2⟩ := h
  rcases ha with rfl | rfl
  · rw [show (if (0 : ℝ) = 0 then (0 : ℕ) else 2 ^ K - 1) = 0 by simp]
    have h3 : (I : ℝ) * (s / 2 ^ K) ≤ 0 * (s / 2 ^ K) := by linarith
    have h4 : (I : ℝ) ≤ 0 := le_of_mul_le_mul_right h3 hpos
    exact_mod_cast le_antisymm (by exact_mod_cast h4) (Nat.zero_le I)
  · rw [show (if -s = 0 then (0 : ℕ) else 2 ^ K - 1) = 2 ^ K - 1 by simp [hs.ne']]
    have h3 : ((2 : ℝ) ^ K) * (s / 2 ^ K) ≤ ((I : ℝ) + 1) * (s / 2 ^ K) := by linarith
    have h4 : (2 : ℝ) ^ K ≤ (I : ℝ) + 1 := le_of_mul_le_mul_right h3 hpos
    have h5 : 2 ^ K ≤ I + 1 := by exact_mod_cast h4
    omega

/-- **Corner cell.**  Let `S = [a, a + s] × [b, b + s]` with `s > 0` and `a, b ∈ {0, -s}`.  A level-`K`
closed dyadic subsquare of `S` with indices `I, J < 2 ^ K` that contains the origin is the corner cell
of `S` at the origin. -/
theorem eq_cornerIndex_of_zero_mem_closedDyadicSubsquare {a b s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s)
    (hb : b = 0 ∨ b = -s) {K I J : ℕ} (hI : I < 2 ^ K) (hJ : J < 2 ^ K)
    (h0 : (0 : ℂ) ∈ closedDyadicSubsquare a b s K I J) :
    I = (if a = 0 then 0 else 2 ^ K - 1) ∧ J = (if b = 0 then 0 else 2 ^ K - 1) := by
  rw [closedDyadicSubsquare_eq_reProdIm, Complex.mem_reProdIm] at h0
  exact ⟨eq_cornerIndex_of_zero_mem_Icc hs ha hI (by simpa using h0.1),
    eq_cornerIndex_of_zero_mem_Icc hs hb hJ (by simpa using h0.2)⟩

end LatticeProb.LQG
