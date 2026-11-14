import LatticeProb.Analysis.ConeVectorFactorialGridCover
import LatticeProb.Prob.CorrelatedBMFactorialModulus
import LatticeProb.Prob.CorrelatedBMConeJointExit

/-!
# Grid barriers for Brownian cone vectors

A single almost-sure event supplies factorial-grid barriers for cone vectors
in both time orientations, at every subcritical modulus exponent.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Almost surely, factorial-grid barriers hold eventually for each separated
backward cone vector, simultaneously in both time orientations. -/
theorem ae_factorial_backwardConeVector_grid_barriers {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ (α : ℝ≥0), (α : ℝ) < 1 / 2 → ∀ C d q : ℝ,
      0 < C → 0 < d → 0 < q → ∀ direction : ℝ, direction = 1 ∨ direction = -1 →
      let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
      let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
      ∃ H : ℝ, 0 < H ∧ ∀ a s : ℝ,
        (a, s) ∈ backwardConeVectors X Y → 0 < a → s < 1 → d < s - a →
        q < s - coneFirstExitBackward X Y s →
        ∀ᶠ n : ℕ in atTop,
          ∃ i j : Fin (n.factorial ^ 6),
            let t₀ : ℝ := (i.val : ℝ) / (n.factorial ^ 6 : ℕ)
            let t₁ : ℝ := (j.val : ℝ) / (n.factorial ^ 6 : ℕ)
            let error : ℝ := C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ (α : ℝ)
            0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
            |t₀ - a| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) ∧
            |t₁ - s| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) ∧
            (((∀ u ∈ Icc 0 H, X t₀ - error ≤ X (t₀ + u)) ∧
              (∀ u ∈ Icc 0 H, X t₁ - error ≤ X (t₁ - u) ∧
                Y t₁ - error ≤ Y (t₁ - u)) ∧
              |X t₁ - X t₀| ≤ error ∧
              ∀ x ∈ Icc t₀ t₁, X t₁ - error ≤ X x) ∨
            ((∀ u ∈ Icc 0 H, Y t₀ - error ≤ Y (t₀ + u)) ∧
              (∀ u ∈ Icc 0 H, Y t₁ - error ≤ Y (t₁ - u) ∧
                X t₁ - error ≤ X (t₁ - u)) ∧
              |Y t₁ - Y t₀| ≤ error ∧
              ∀ x ∈ Icc t₀ t₁, Y t₁ - error ≤ Y x)) := by
  filter_upwards [ae_factorial_modulus hμ, ae_forall_strict_drop_time_orientation hμ] with ω hmod hdrop
  intro α hα C d q hC hd hq direction hdir
  let X : ℝ → ℝ := fun t => lrCoord 0 (direction * t) ω
  let Y : ℝ → ℝ := fun t => lrCoord 1 (direction * t) ω
  let e : ℕ → ℝ := fun n => (C / 2) * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ (α : ℝ)
  have hm : ∀ᶠ n in atTop, ∀ x ∈ Icc (-2 : ℝ) 2, ∀ y ∈ Icc (-2 : ℝ) 2,
      |x - y| ≤ 1 / ((n.factorial ^ 6 : ℕ) : ℝ) →
      |X x - X y| ≤ e n ∧ |Y x - Y y| ≤ e n := by
    filter_upwards [hmod α hα (C / 2) (by linarith)] with n hn x hx y hy hxy
    exact ⟨hn 0 direction hdir x hx y hy hxy, hn 1 direction hdir x hx y hy hxy⟩
  obtain ⟨H, hH, hcover⟩ := exists_horizon_eventually_factorial_backwardConeVector_grid_barriers
    ((continuous_lrCoord_time 0 ω).comp (continuous_const.mul continuous_id))
    ((continuous_lrCoord_time 1 ω).comp (continuous_const.mul continuous_id)) hd hq e hm
  refine ⟨H, hH, ?_⟩
  intro a s hv ha hs hsep hgap
  have hc := hcover a s (hdrop 0 s direction hdir) (hdrop 1 s direction hdir)
    hv ha hs hsep hgap
  filter_upwards [hc] with n hn
  have he : 2 * e n = C * (1 / ((n.factorial ^ 6 : ℕ) : ℝ)) ^ (α : ℝ) := by
    dsimp [e]
    ring
  rcases hn with ⟨i, j, hn⟩
  refine ⟨i, j, ?_⟩
  rw [he] at hn
  exact hn

end LatticeProb.CorrelatedBM
