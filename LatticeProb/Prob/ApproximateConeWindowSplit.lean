/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.ApproximateConeGridEvent

/-!
# Window decomposition of an approximate cone event

The local barriers and endpoint condition can be expressed using increments on
three consecutive time windows. This form is useful for independent increments.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Shortening the local windows preserves the two barriers, and decomposes the
endpoint increment through the intervening window. -/
theorem approximateConeGridEvent_window_split {Ω : Type*} {X Y : Ω → ℝ → ℝ}
    {E : Ω → ℝ} {a b H h : ℝ} {ω : Ω} (hh : h ≤ H)
    (hevent : ω ∈ approximateConeGridEvent X Y E a b H) :
    (∀ u ∈ Icc 0 h, -E ω ≤ X ω (a + u) - X ω a) ∧
    (∀ u ∈ Icc 0 h, -E ω ≤ X ω (b - u) - X ω b ∧
      -E ω ≤ Y ω (b - u) - Y ω b) ∧
    |(X ω (b - h) - X ω (a + h)) +
        (X ω (a + h) - X ω a) - (X ω (b - h) - X ω b)| ≤ E ω := by
  rcases hevent with ⟨hf, hb, hi, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    have hs := hf u ⟨hu.1, hu.2.trans hh⟩
    linarith
  · intro u hu
    obtain ⟨hx, hy⟩ := hb u ⟨hu.1, hu.2.trans hh⟩
    constructor <;> linarith
  · have hid : (X ω (b - h) - X ω (a + h)) +
        (X ω (a + h) - X ω a) - (X ω (b - h) - X ω b) =
        X ω b - X ω a := by ring
    rw [hid]
    exact hi

end LatticeProb
