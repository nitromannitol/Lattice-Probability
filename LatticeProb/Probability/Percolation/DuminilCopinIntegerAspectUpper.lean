import LatticeProb.Probability.Percolation.DuminilCopinIntegerAspect

/-!
# Upper bounds for integer rectangle crossings

Critical planar duality and the integer aspect ratio lower bound give a uniform
upper bound for crossing probabilities of inclusive integer rectangles.
-/

open ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

/-- Critical crossings of every positive integer aspect ratio are uniformly bounded away from one. -/
theorem exists_pos_integer_aspect_crossing_upper (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → crossingProb half (k * n) (2 * n) ≤ 1 - c := by
  obtain ⟨c, hc, hlower⟩ := exists_pos_integer_aspect_crossing 8 (by omega)
  refine ⟨min c ((1 / 2 : ℝ) ^ 9), lt_min hc (by positivity), ?_⟩
  intro n hn
  have hkn : 1 ≤ k * n := by nlinarith
  have hdual := crossingProb_add_crossingProb_symm_holds half (k * n - 1) (2 * n)
  rw [symm_half, Nat.sub_add_cancel hkn] at hdual
  have hbound : min c ((1 / 2 : ℝ) ^ 9) ≤ crossingProb half (2 * n + 1) (k * n - 1) := by
    by_cases hs : n < 5
    · have hp := pow_le_crossingProb half 9 (k * n - 1)
      change (1 / 2 : ℝ) ^ 9 ≤ _ at hp
      exact (min_le_right _ _).trans (hp.trans (crossingProb_anti_left half (by omega) _))
    · let r := (n - 1) / 2
      have hr : 1 ≤ r := by dsimp [r]; omega
      have hw : 2 * n + 1 ≤ 8 * r := by dsimp [r]; omega
      have hh : 2 * r ≤ k * n - 1 := by
        have : n ≤ k * n := by nlinarith
        dsimp [r]
        omega
      exact (min_le_left _ _).trans ((hlower r hr).trans
        ((crossingProb_anti_left half hw _).trans (crossingProb_mono_right half _ hh)))
  linarith

end EdgeCrossing
