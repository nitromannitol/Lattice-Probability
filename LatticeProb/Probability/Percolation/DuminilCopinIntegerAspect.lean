import LatticeProb.Probability.Percolation.DuminilCopinIntegerGluing

/-!
# Integer aspect ratio crossing bounds

The critical crossing bound for a `3n` by `2n` rectangle extends to all
integer aspect ratios by gluing and positive association.
-/

open ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

private theorem integer_long_crossing (n : ℕ) (hn : 1 ≤ n) (t : ℕ) :
    (1 / 128 : ℝ) * (1 / 256 : ℝ) ^ t ≤
      crossingProb half (3 * n + t * n) (2 * n) := by
  induction t with
  | zero => simpa using one_div_128_le_integer_rectangle_crossing n hn
  | succ t ih =>
    have hw : 3 * n + (t + 1) * n =
        (3 * n + t * n) + 3 * n - 2 * n := by
      have : (t + 1) * n = t * n + n := by ring
      omega
    have hg := crossingProb_glue_holds half (3 * n + t * n) (3 * n) (2 * n)
      (by omega) (by omega)
    rw [← hw] at hg
    have hB := one_div_128_le_integer_rectangle_crossing n hn
    have hC := half_le_crossingProb_self crossingProb_half_succ_self_holds (2 * n)
    have h0 : ∀ a b : ℕ, (0 : ℝ) ≤ crossingProb half a b :=
      fun a b => (crossingProb_mem_Icc _ _ _).1
    calc
      (1 / 128 : ℝ) * (1 / 256 : ℝ) ^ (t + 1) =
          ((1 / 128 : ℝ) * (1 / 256 : ℝ) ^ t) * (1 / 128) * (1 / 2) := by
            rw [pow_succ]
            ring
      _ ≤ crossingProb half (3 * n + t * n) (2 * n) *
            crossingProb half (3 * n) (2 * n) * crossingProb half (2 * n) (2 * n) :=
        mul_le_mul (mul_le_mul ih hB (by positivity) (h0 _ _)) hC (by norm_num)
          (mul_nonneg (h0 _ _) (h0 _ _))
      _ ≤ crossingProb half (3 * n + (t + 1) * n) (2 * n) := hg

/-- Every positive integer aspect ratio has a uniform positive critical crossing bound. -/
theorem exists_pos_integer_aspect_crossing (k : ℕ) (_hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c ≤ crossingProb half (k * n) (2 * n) := by
  refine ⟨(1 / 128 : ℝ) * (1 / 256 : ℝ) ^ k, by positivity, ?_⟩
  intro n hn
  exact (integer_long_crossing n hn k).trans
    (crossingProb_anti_left half (by omega) (2 * n))

end EdgeCrossing
