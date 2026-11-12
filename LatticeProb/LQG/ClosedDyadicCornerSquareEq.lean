import LatticeProb.LQG.ClosedDyadicCornerCell

/-!
# The corner cell as an explicit product of intervals

Let `S = [a, a + s] × [b, b + s]` with `s > 0` and `a, b ∈ {0, -s}`, so that the origin is a corner of `S`.
A level-`m` closed dyadic subsquare of `S` that contains the origin is the corner cell
`[a 2⁻ᵐ, a 2⁻ᵐ + s 2⁻ᵐ] × [b 2⁻ᵐ, b 2⁻ᵐ + s 2⁻ᵐ]`, the dilate of `S` by the factor `2⁻ᵐ`.

## Main statement

* `LatticeProb.LQG.closedDyadicSubsquare_cornerIndex_eq`.
-/

open Set

namespace LatticeProb.LQG

/-- The left endpoint of the corner cell of level `K` is `a / 2 ^ K` when `a ∈ {0, -s}`. -/
theorem add_cornerIndex_mul_eq {a s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s) {K I : ℕ}
    (hI : I = if a = 0 then 0 else 2 ^ K - 1) :
    a + I * (s / 2 ^ K) = a / 2 ^ K := by
  rcases ha with rfl | rfl
  · rw [show (if (0 : ℝ) = 0 then (0 : ℕ) else 2 ^ K - 1) = 0 by simp] at hI
    subst hI
    simp
  · rw [show (if -s = 0 then (0 : ℕ) else 2 ^ K - 1) = 2 ^ K - 1 by simp [hs.ne']] at hI
    subst hI
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
    push_cast
    field_simp
    ring

/-- **The corner cell as a product of intervals.**  Let `S = [a, a + s] × [b, b + s]` with `s > 0` and
`a, b ∈ {0, -s}`.  A level-`m` closed dyadic subsquare of `S` with indices `i, j < 2 ^ m` that contains the
origin equals `[a 2⁻ᵐ, a 2⁻ᵐ + s 2⁻ᵐ] × [b 2⁻ᵐ, b 2⁻ᵐ + s 2⁻ᵐ]`. -/
theorem closedDyadicSubsquare_cornerIndex_eq {a b s : ℝ} (hs : 0 < s) (ha : a = 0 ∨ a = -s)
    (hb : b = 0 ∨ b = -s) {m i j : ℕ} (hi : i < 2 ^ m) (hj : j < 2 ^ m)
    (h0 : (0 : ℂ) ∈ closedDyadicSubsquare a b s m i j) :
    closedDyadicSubsquare a b s m i j =
      Icc (a / 2 ^ m) (a / 2 ^ m + s / 2 ^ m) ×ℂ Icc (b / 2 ^ m) (b / 2 ^ m + s / 2 ^ m) := by
  obtain ⟨hi', hj'⟩ := eq_cornerIndex_of_zero_mem_closedDyadicSubsquare hs ha hb hi hj h0
  rw [closedDyadicSubsquare_eq_reProdIm, add_cornerIndex_mul_eq hs ha hi',
    add_cornerIndex_mul_eq hs hb hj']

end LatticeProb.LQG
