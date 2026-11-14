import LatticeProb.Prob.CorrelatedBMForwardConeGridCover
import LatticeProb.Prob.CorrelatedBMConeGridEvents

/-!
# Measurable grid events for forward Brownian cone vectors

Reflected forward vectors are covered by a countable family of measurable
factorial-grid events with a common horizon for each separated class.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Almost surely, reflected separated forward cone vectors have eventual
factorial-grid event covers, simultaneously in both time orientations. -/
theorem ae_factorial_forwardConeVector_reflected_grid_events {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (α : ℝ≥0), (α : ℝ) < 1 / 2 → ∀ C d : ℝ,
      0 < C → 0 < d → ∀ direction : ℝ, direction = 1 ∨ direction = -1 →
      let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
      ∃ k : ℕ, ∀ a s : ℝ,
        (a, s) ∈ forwardConeVectors X Y → 0 < -a → -s < 1 → d < -s - -a →
        ∀ᶠ n : ℕ in atTop,
          ∃ i j : Fin (n.factorial ^ 6),
            let t₀ : ℝ := (i.val : ℝ) / (n.factorial ^ 6 : ℕ)
            let t₁ : ℝ := (j.val : ℝ) / (n.factorial ^ 6 : ℕ)
            0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
            |t₀ - -a| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) ∧
            |t₁ - -s| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) ∧
            ω ∈ factorialConeGridEvent (-direction) C α k n i j := by
  filter_upwards [ae_factorial_forwardConeVector_reflected_grid_barriers hμ] with ω hω
  intro α hα C d hC hd direction hdir
  obtain ⟨H, hH, hcover⟩ := hω α hα C d hC hd direction hdir
  let X : Path2 → ℝ → ℝ := fun ω t => lrCoord 0 (-direction * t) ω
  let Y : Path2 → ℝ → ℝ := fun ω t => lrCoord 1 (-direction * t) ω
  obtain ⟨k, _, hk⟩ := exists_reciprocal_approximateConeGridEvent_subset X Y hH
  refine ⟨k, ?_⟩
  intro a s hv ha hs hsep
  filter_upwards [hcover a s hv ha hs hsep] with n hn
  obtain ⟨i, j, h₀, h₁, hsep', ha', hs', hevent⟩ := hn
  refine ⟨i, j, h₀, h₁, hsep', ha', hs', ?_⟩
  apply hk
  simpa only [X, Y, approximateConeGridEvent, mem_union, mem_ofPred_eq,
    neg_mul, mul_neg] using hevent

end LatticeProb.CorrelatedBM
