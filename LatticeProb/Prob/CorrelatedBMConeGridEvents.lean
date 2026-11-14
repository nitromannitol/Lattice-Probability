/-
Copyright (c) 2026. Released under the Apache 2.0 license.
-/
import LatticeProb.Prob.CorrelatedBMConeGridCover
import LatticeProb.Prob.ApproximateConeGridHorizon

/-!
# Measurable grid events for Brownian cone vectors

A countable family of measurable fixed-horizon events covers the factorial-grid
barriers, with a common horizon for every cone vector in a separated class.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- The two possible coordinate orientations of the factorial-grid barrier. -/
def factorialConeGridEvent (direction C α : ℝ) (k n : ℕ)
    (i j : Fin (n.factorial ^ 6)) : Set Path2 :=
  let X : Path2 → ℝ → ℝ := fun ω t => lrCoord 0 (direction * t) ω
  let Y : Path2 → ℝ → ℝ := fun ω t => lrCoord 1 (direction * t) ω
  let E : Path2 → ℝ := fun _ => C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ α
  let a : ℝ := (i.val : ℝ) / (n.factorial ^ 6 : ℕ)
  let b : ℝ := (j.val : ℝ) / (n.factorial ^ 6 : ℕ)
  approximateConeGridEvent X Y E a b (1 / (k + 1 : ℝ)) ∪
    approximateConeGridEvent Y X E a b (1 / (k + 1 : ℝ))

/-- Every fixed member of the factorial-grid event family is measurable. -/
theorem measurableSet_factorialConeGridEvent (direction C α : ℝ) (k n : ℕ)
    (i j : Fin (n.factorial ^ 6)) :
    MeasurableSet (factorialConeGridEvent direction C α k n i j) := by
  apply measurableSet_approximateConeGridEvent_union
  · intro ω
    exact (continuous_lrCoord_time 0 ω).comp (continuous_const.mul continuous_id)
  · intro ω
    exact (continuous_lrCoord_time 1 ω).comp (continuous_const.mul continuous_id)
  · intro t
    exact measurable_lrCoord (0, direction * t)
  · intro t
    exact measurable_lrCoord (1, direction * t)
  · exact measurable_const

/-- Almost surely one reciprocal horizon works for all separated cone vectors;
the eventual scale may depend on the vector. -/
theorem ae_factorial_backwardConeVector_grid_events {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (α : ℝ≥0), (α : ℝ) < 1 / 2 → ∀ C d q : ℝ,
      0 < C → 0 < d → 0 < q → ∀ direction : ℝ, direction = 1 ∨ direction = -1 →
      let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
      ∃ k : ℕ, ∀ a s : ℝ,
        (a, s) ∈ backwardConeVectors X Y → 0 < a → s < 1 → d < s - a →
        q < s - coneFirstExitBackward X Y s →
        ∀ᶠ n : ℕ in atTop,
          ∃ i j : Fin (n.factorial ^ 6),
            let t₀ : ℝ := (i.val : ℝ) / (n.factorial ^ 6 : ℕ)
            let t₁ : ℝ := (j.val : ℝ) / (n.factorial ^ 6 : ℕ)
            0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
            |t₀ - a| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) ∧
            |t₁ - s| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) ∧
            ω ∈ factorialConeGridEvent direction C α k n i j := by
  filter_upwards [ae_factorial_backwardConeVector_grid_barriers hμ] with ω hω
  intro α hα C d q hC hd hq direction hdir
  obtain ⟨H, hH, hcover⟩ := hω α hα C d q hC hd hq direction hdir
  let X : Path2 → ℝ → ℝ := fun ω t => lrCoord 0 (direction * t) ω
  let Y : Path2 → ℝ → ℝ := fun ω t => lrCoord 1 (direction * t) ω
  obtain ⟨k, _, hk⟩ := exists_reciprocal_approximateConeGridEvent_subset X Y hH
  refine ⟨k, ?_⟩
  intro a s hv ha hs hsep hgap
  filter_upwards [hcover a s hv ha hs hsep hgap] with n hn
  obtain ⟨i, j, h₀, h₁, hsep', ha', hs', hevent⟩ := hn
  refine ⟨i, j, h₀, h₁, hsep', ha', hs', ?_⟩
  exact hk _ _ _ hevent

end LatticeProb.CorrelatedBM
