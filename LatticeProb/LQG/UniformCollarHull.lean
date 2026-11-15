import LatticeProb.LQG.DyadicHullNeighborhoods

/-! # Uniform dyadic hulls inside collars -/

set_option autoImplicit false

open Set Metric
open LQGMetric.Blueprint LQGMetric.LocalEvent LQGMetric.CONF

namespace LatticeProb.LQG

/-- A positive collar contains a dyadic hull at a scale independent of the set. -/
theorem exists_uniform_dyadicHull_subset_thickening {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ A : Set ℂ, dyadicHull n A ⊆ thickening ε A := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hn' : (2 : ℝ) / 2 ^ n < ε := by
    rw [one_div_pow] at hn
    have heq : (2 : ℝ) / 2 ^ n = 2 * (1 / 2 ^ n) := by ring
    rw [heq]
    linarith
  refine ⟨n, fun A x hx => ?_⟩
  simp only [dyadicHull, mem_iUnion] at hx
  obtain ⟨k, ⟨y, hyk, hyA⟩, hxk⟩ := hx
  exact mem_thickening_iff.2 ⟨y, hyA, lt_of_le_of_lt (conf21_sq_dist hxk hyk) hn'⟩

/-- Reciprocal collars admit deterministic enclosing-hull scales simultaneously. -/
theorem exists_dyadicHull_scales_subset_reciprocal_thickening :
    ∃ f : ℕ → ℕ, ∀ k (A : Set ℂ), dyadicHull (f k) A ⊆
      thickening (1 / ((k : ℝ) + 1)) A := by
  have h : ∀ k : ℕ, ∃ n : ℕ, ∀ A : Set ℂ, dyadicHull n A ⊆
      thickening (1 / ((k : ℝ) + 1)) A := by
    intro k
    exact exists_uniform_dyadicHull_subset_thickening (by positivity)
  choose f hf using h
  exact ⟨f, hf⟩

end LatticeProb.LQG
