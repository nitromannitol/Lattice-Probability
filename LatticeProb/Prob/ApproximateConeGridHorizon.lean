/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.ApproximateConeGridEvent

/-!
# Horizons for approximate cone-vector events

Decreasing the local horizon preserves the approximate event, including its
interval and increment conditions. A countable family of positive reciprocal
horizons suffices uniformly for all anchors and error functions.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A shorter local horizon preserves all the approximate barriers. -/
theorem approximateConeGridEvent_mono_horizon {Ω : Type*} (X Y : Ω → ℝ → ℝ)
    (E : Ω → ℝ) (a b : ℝ) {H H' : ℝ} (hH : H' ≤ H) :
    approximateConeGridEvent X Y E a b H ⊆ approximateConeGridEvent X Y E a b H' := by
  intro ω h
  rcases h with ⟨hf, hb, hi⟩
  refine ⟨?_, ?_, hi⟩
  · intro u hu
    exact hf u ⟨hu.1, hu.2.trans hH⟩
  · intro u hu
    exact hb u ⟨hu.1, hu.2.trans hH⟩

/-- A positive horizon admits a smaller reciprocal horizon, uniformly over
all grid anchors, errors, and both coordinate orientations. -/
theorem exists_reciprocal_approximateConeGridEvent_subset {Ω : Type*}
    (X Y : Ω → ℝ → ℝ) {H : ℝ} (hH : 0 < H) :
    ∃ k : ℕ, 0 < 1 / (k + 1 : ℝ) ∧ ∀ (E : Ω → ℝ) (a b : ℝ),
      (approximateConeGridEvent X Y E a b H ∪ approximateConeGridEvent Y X E a b H) ⊆
      (approximateConeGridEvent X Y E a b (1 / (k + 1 : ℝ)) ∪
       approximateConeGridEvent Y X E a b (1 / (k + 1 : ℝ))) := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hH
  refine ⟨k, by positivity, ?_⟩
  intro E a b ω hω
  rcases hω with hω | hω
  · exact Or.inl (approximateConeGridEvent_mono_horizon X Y E a b (le_of_lt hk) hω)
  · exact Or.inr (approximateConeGridEvent_mono_horizon Y X E a b (le_of_lt hk) hω)

end LatticeProb
