import LatticeProb.Probability.Percolation.DuminilCopinIntegerTwoSided

/-!
# Critical crossing bounds for integer rectangles

Crossing probabilities of rectangles with a fixed positive integer aspect ratio
are uniformly bounded away from zero and one at criticality.
-/

open ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

/-- Critical crossings of rectangles of any positive integer height have two-sided bounds. -/
theorem exists_pos_all_integer_heights_crossing_two_sided (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ crossingProb half (k * n) n ∧
        crossingProb half (k * n) n ≤ 1 - c := by
  obtain ⟨a, ha, hlower⟩ := exists_pos_integer_aspect_crossing (3 * k) (by omega)
  obtain ⟨b, hb, hupper⟩ := exists_pos_integer_aspect_crossing_upper k hk
  refine ⟨min (min a ((1 / 2 : ℝ) ^ k)) b, lt_min (lt_min ha (by positivity)) hb, ?_⟩
  intro n hn
  constructor
  · by_cases hsmall : n = 1
    · subst n
      have hp := pow_le_crossingProb half k 1
      change (1 / 2 : ℝ) ^ k ≤ _ at hp
      simpa using (min_le_left (min a ((1 / 2 : ℝ) ^ k)) b).trans
        ((min_le_right a ((1 / 2 : ℝ) ^ k)).trans hp)
    · let m := n / 2
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hnupper : n ≤ 3 * m := by dsimp [m]; omega
      have hnlower : 2 * m ≤ n := by dsimp [m]; omega
      have hw : k * n ≤ 3 * k * m := by nlinarith
      exact (min_le_left _ _).trans ((min_le_left _ _).trans
        ((hlower m hm).trans ((crossingProb_anti_left half hw _).trans
          (crossingProb_mono_right half _ hnlower))))
  · exact (crossingProb_mono_right half (k * n) (by omega)).trans
      ((hupper n hn).trans (sub_le_sub_left (min_le_right _ _) 1))

end EdgeCrossing
