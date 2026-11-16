import LatticeProb.Probability.Percolation.DuminilCopinIntegerAspectUpper

/-!
# Two-sided bounds for integer rectangle crossings

At criticality, crossing probabilities for rectangles with a fixed positive
integer aspect ratio stay uniformly away from both zero and one.
-/

open ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

/-- Critical crossings of every positive integer aspect ratio admit a common two-sided bound. -/
theorem exists_pos_integer_aspect_crossing_two_sided (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ crossingProb half (k * n) (2 * n) ∧
        crossingProb half (k * n) (2 * n) ≤ 1 - c := by
  obtain ⟨a, ha, hlower⟩ := exists_pos_integer_aspect_crossing k hk
  obtain ⟨b, hb, hupper⟩ := exists_pos_integer_aspect_crossing_upper k hk
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro n hn
  exact ⟨(min_le_left _ _).trans (hlower n hn),
    (hupper n hn).trans (sub_le_sub_left (min_le_right _ _) 1)⟩

end EdgeCrossing
