import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic
import LatticeProb.Prob.AkcogluKrengelAE.BallMaximalLp
import LatticeProb.Prob.AkcogluKrengel

/-!
# The `Lᵖ` box mean ergodic theorem, and the pair-to-anchored-box reduction

Source main read: `01de1d0`.  `LatticeProb.akcoglu_krengel_mean` (`Prob/AkcogluKrengel.lean:730`) is
a *scalar* cube statement, not an `Lᵖ` norm convergence, so it does not supply the mean half.  The
library's `KrengelLpBall` (`BallMaximalLp.lean:74`) is the `ℓ¹`-ball `Lᵖ` maximal bound (the maximal
half); a box is contained in an `ℓ¹` ball, so it dominates the box maximal.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The normalized anchored-box average of `h` at scale `N`. -/
noncomputable def anchoredBoxAvgMean (h : Ω → ℝ) (τ : Site d → Ω → Ω) (c : Fin d → ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, h (τ x ω)

/-- **The anchored-box `Lᵖ` maximal inequality.**  For `c ≥ 0` and `p > 1`, the sup over `N` of the
deviation of the box average from the mean is controlled in `Lᵖ` by `‖h - ∫h‖_p`. -/
def AnchoredBoxMaximal (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Ω → ℝ), Measurable h →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      ∫⁻ ω, (⨆ N : ℕ,
          ENNReal.ofReal |anchoredBoxAvgMean h τ c N ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) ^ p ∂μ ≤
        ENNReal.ofReal C *
          ∫⁻ ω, (ENNReal.ofReal |h ω - ∫ ω, h ω ∂μ|) ^ p ∂μ

/-- **The `Lᵖ` box mean ergodic theorem**: `∫⁻ |boxAvg_N h - (∏ᵢ cᵢ) ∫h|ᵖ → 0`. -/
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

/-- **The dense-class input of the upgrade.**  A class of bounded measurable functions, dense in
`Lᵖ` modulo constants, on which the box averages converge a.e. to the mean. -/
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

/-- **Step (c): the density/`limsup` upgrade.**  Given the maximal inequality and the dense class,
every bounded measurable `h` has its box averages converging a.e. to `(∏ᵢ cᵢ) ∫h`: for `g` in the
class, `limsup_N |A_N h| ≤ limsup_N |A_N g| + sup_N |A_N (h - g)| = sup_N |A_N (h - g)|` a.e., the
maximal bound controls the sup in `Lᵖ`, and the `Lᵖ` density lets `∫ |(h-g) - ∫(h-g)|ᵖ → 0`. -/
def AnchoredBoxDensityUpgrade (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) → 1 < p →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    AnchoredBoxMaximal d c p → AnchoredBoxDenseClass d c p →
    ∀ (h : Ω → ℝ), Measurable h → (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => anchoredBoxAvgMean h τ c N ω) atTop
        (𝓝 ((∏ i, c i) * ∫ ω, h ω ∂μ))

/-- **The pair-to-anchored-box reduction.**  With the `Lᵖ` maximal inequality `AnchoredBoxMaximal`
(the library's `KrengelLpBall` dominates it), the `Lᵖ` box mean theorem `AnchoredBoxMean` and the
dense/`limsup` upgrade `AnchoredBoxDensityUpgrade`, the library's `AnchoredBoxErgodic` holds.  The
upgrade is the only place the density/`limsup` argument is used. -/
theorem AnchoredBoxErgodic_of_MaximalMean
    (Hmax : ∀ (c : Fin d → ℝ) (p : ℝ), 1 < p → AnchoredBoxMaximal d c p)
    (_Hmean : ∀ (c : Fin d → ℝ) (p : ℝ), 1 < p → AnchoredBoxMean d c p)
    (Hdense : ∀ (c : Fin d → ℝ) (p : ℝ), 1 < p → AnchoredBoxDenseClass d c p)
    (Hup : ∀ (c : Fin d → ℝ) (p : ℝ), 1 < p → AnchoredBoxDensityUpgrade d c p) :
    AnchoredBoxErgodic d := by
  intro Ω _ μ _ τ hτ hadd _herg h hh hb c hc
  exact (Hup c 2 (by norm_num)) hc (by norm_num) μ τ hτ hadd
    (Hmax c 2 (by norm_num)) (Hdense c 2 (by norm_num)) h hh hb

end LatticeProb
