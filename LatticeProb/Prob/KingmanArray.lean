import Mathlib
import LatticeProb.Prob.Kingman

/-!
# Kingman's theorem for a two-index array, with the limit identified

For a nonnegative integrable measurable array `X m n` that is stationary under a
measure-preserving `θ` and subadditive in the middle index, the first row `X 0 n`
is subadditive along `θ`, so `X 0 n / n` converges almost everywhere to the
lower limit `gLow (X 0)`, which is measurable and almost everywhere invariant.
-/

open MeasureTheory Filter Topology

universe u

namespace LatticeProb

/-- Stationarity iterated: shifting the point by `θ^[k]` shifts both indices by `k`. -/
theorem kingmanArray_iterate {Ω : Type*} {θ : Ω → Ω} {X : ℕ → ℕ → Ω → ℝ}
    (hstat : ∀ m n ω, X m n (θ ω) = X (m + 1) (n + 1) ω) :
    ∀ (k m n : ℕ) (ω : Ω), X m n (θ^[k] ω) = X (m + k) (n + k) ω := by
  intro k
  induction k with
  | zero => intro m n ω; simp
  | succ k ih =>
    intro m n ω
    rw [Function.iterate_succ_apply, ih m n (θ ω), hstat (m + k) (n + k) ω]
    rfl

/-- The first row of a stationary, middle-index subadditive array is subadditive along `θ`. -/
theorem kingmanArray_subadditiveAlong {Ω : Type*} {θ : Ω → Ω} {X : ℕ → ℕ → Ω → ℝ}
    (hstat : ∀ m n ω, X m n (θ ω) = X (m + 1) (n + 1) ω)
    (hsub : ∀ l m n ω, l ≤ m → m ≤ n → X l n ω ≤ X l m ω + X m n ω) :
    SubadditiveAlong θ (X 0) := by
  intro m n ω
  have h := hsub 0 m (m + n) ω (Nat.zero_le _) (Nat.le_add_right _ _)
  have h2 : X 0 n (θ^[m] ω) = X m (m + n) ω := by
    rw [kingmanArray_iterate hstat m 0 n ω]
    simp [Nat.add_comm]
  rw [h2]
  exact h

/-- **Kingman's subadditive ergodic theorem in array form** (the form the rotor project consumes).
For a probability measure `μ`, a measure-preserving `θ` and a nonnegative integrable measurable array
`X m n` that is stationary (`X m n ∘ θ = X (m+1) (n+1)`) and subadditive in the middle index, the
ratios `X 0 n / n` converge almost everywhere to a measurable, almost everywhere `θ`-invariant
limit (namely `gLow (X 0)`).  The expectation bound `∫ X 0 n ≤ c n` is not needed for this
conclusion. -/
theorem kingman_array :
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ θ : Ω → Ω, MeasurePreserving θ μ μ →
        ∀ X : ℕ → ℕ → Ω → ℝ,
          (∀ m n, Measurable (X m n)) →
          (∀ m n, Integrable (X m n) μ) →
          (∀ m n ω, 0 ≤ X m n ω) →
          (∀ m n ω, X m n (θ ω) = X (m + 1) (n + 1) ω) →
          (∀ l m n ω, l ≤ m → m ≤ n → X l n ω ≤ X l m ω + X m n ω) →
          (∃ c : ℝ, ∀ n, ∫ ω, X 0 n ω ∂μ ≤ c * n) →
          ∃ γ : Ω → ℝ, Measurable γ ∧ (∀ᵐ ω ∂μ, γ (θ ω) = γ ω) ∧
            ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => X 0 n ω / n) atTop (𝓝 (γ ω)) := by
  intro Ω _ μ hμ θ hθ X hmeas hint hnonneg hstat hsub _
  have hsub' : SubadditiveAlong θ (X 0) := kingmanArray_subadditiveAlong hstat hsub
  have hg : ∀ n ω, 1 ≤ n → 0 ≤ X 0 n ω := fun n ω _ => hnonneg 0 n ω
  have hgm : ∀ n, Measurable (X 0 n) := fun n => hmeas 0 n
  refine ⟨gLow (X 0), measurable_gLow hgm, ae_gLow_comp hθ hsub' hg hgm (hint 0 1), ?_⟩
  exact ae_tendsto_gLow hθ hsub' hg hgm (hint 0 1)

end LatticeProb
