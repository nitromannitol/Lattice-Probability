import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic
import LatticeProb.Prob.AkcogluKrengelAE.BallMaximalLp
import LatticeProb.Prob.AkcogluKrengel

/-!
# The `Lᵖ` box mean ergodic theorem, and the pair-to-anchored-box reduction

Source main read: `01de1d0`.  The library has `LatticeProb.akcoglu_krengel_mean`
(`Prob/AkcogluKrengel.lean:730`), the *mean* multiparameter ergodic theorem, but it is a scalar
statement: `(∫ ω, f (latticeCube d n) ω) / n^d → L`, not an `Lᵖ` norm convergence, and it is along
cubes only.  The `Lᵖ` box mean theorem below is the half of the anchored-box gap not covered by the
maximal inequality `AnchoredBoxMaximal` (`AnchoredBoxMaximal.lean`).

`BallMaximalLp.lean` (already in this worktree, not written by me) states `BirkhoffLpMaximal` and
`KrengelLpBall`, the `Lᵖ` *maximal* bounds, and proves nothing of them; it is the maximal half, not
the mean half.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The normalized anchored-box average of `h` at scale `N`. -/
noncomputable def anchoredBoxAvgMean (h : Ω → ℝ) (τ : Site d → Ω → Ω) (c : Fin d → ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, h (τ x ω)

/-- **The `Lᵖ` box mean ergodic theorem.**  For each box shape `c ≥ 0` and `p > 1`, the normalised
box average converges to the mean in `Lᵖ`: `∫⁻ |anchoredBoxAvgMean_N h - (∏ᵢ cᵢ) ∫h|ᵖ → 0`. -/
def AnchoredBoxMean (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      Tendsto (fun N : ℕ =>
          ∫⁻ ω, (ENNReal.ofReal
            |anchoredBoxAvgMean h τ c N ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) ^ p ∂μ)
        atTop (𝓝 0)

/-- **The dense-class input of the upgrade.**  There is a class `D` of bounded measurable
functions, dense in `Lᵖ` modulo constants (for every bounded measurable `h` and every `ε > 0` there
is `g ∈ D` with `∫⁻ |(h - g) - ∫ (h - g)|ᵖ < ε`), on which the box averages converge almost surely
to the mean.  This is step (a) of the standard route (invariant functions plus coboundaries); its
existence is not provided by `akcoglu_krengel_mean`. -/
def AnchoredBoxDenseClass (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∃ D : Set (Ω → ℝ),
      (∀ g ∈ D, Measurable g) ∧
      (∀ g ∈ D, ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ =>
          anchoredBoxAvgMean g τ c N ω - (∏ i, c i) * ∫ ω, g ω ∂μ) atTop (𝓝 0)) ∧
      (∀ h : Ω → ℝ, Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) → ∀ ε : ℝ, 0 < ε →
        ∃ g ∈ D, ∫⁻ ω, (ENNReal.ofReal
          |(h ω - g ω) - ∫ ω', (h ω' - g ω') ∂μ|) ^ p ∂μ < ENNReal.ofReal ε)

/-- **The pair-to-anchored-box reduction, pinned.**  The library's `KrengelLpBall d` (its `ℓ¹`-ball
`Lᵖ` maximal bound, `BallMaximalLp.lean:74`, identical to ds1's `wip/MaximalErgodicReduction.lean`
statement) dominates the box maximal (a box `∏ᵢ [0, ⌈N cᵢ⌉)` is contained in the `ℓ¹` ball of radius
`N ∑ᵢ cᵢ`), and `AnchoredBoxMean`/`AnchoredBoxDenseClass` are the `Lᵖ` mean half.  This `Prop` is the
exact implication whose proof is the remaining `limsup`/`lintegral` assembly: with it (and with
`KrengelLpBall` proved by ds1) the library's `AnchoredBoxErgodic` is discharged, so the library's
gap is pinned to the single missing mean statement. -/
def AnchoredBoxErgodicOfMaximalMean (d : ℕ) : Prop :=
  KrengelLpBall d →
  (∀ (c : Fin d → ℝ), (∀ i, 0 ≤ c i) → ∀ p : ℝ, 1 < p → AnchoredBoxMean d c p) →
  (∀ (c : Fin d → ℝ), (∀ i, 0 ≤ c i) → ∀ p : ℝ, 1 < p → AnchoredBoxDenseClass d c p) →
  AnchoredBoxErgodic d

end LatticeProb
