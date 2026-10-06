import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic
import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityCore
import LatticeProb.Prob.AkcogluKrengelAE.Assembly
import LatticeProb.Prob.AkcogluKrengel

/-!
# The missing anchored-box maximal inequality, as a formal statement

The maximal-inequality directory
proves a maximal inequality only for the **anchored-cube** set function
(`LatticeProb.measureReal_exists_heavy_le_akMaxConst_mul_div`,
`MaximalInequalityCore.lean:443`) and a cube tiling bound
(`LatticeProb.cubeRatio_le_gridAvg_add_defect`, `UpperBound.lean:103`).  Neither covers
coordinate-dependent boxes `∏ᵢ [0, ⌈N cᵢ⌉)`.

`AnchoredBoxMaximal d c p` below is the missing statement, kept measurable and `ℝ≥0∞`-valued: for a
fixed box shape `c ≥ 0` and exponent `p > 1`, the maximal function
`sup_N |N^{-d} Σ_{x ∈ anchoredBox c N} h (τ x ω) - (∏ᵢ cᵢ) ∫ h|` is controlled in `L^p` by
`‖h - ∫ h‖_p`.  The sup is over the countable set `N : ℕ`, so the `⨆` is legitimate in `ℝ≥0∞`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The normalized anchored-box average of `h` at scale `N`. -/
noncomputable def anchoredBoxAvg (h : Ω → ℝ) (τ : Site d → Ω → Ω) (c : Fin d → ℝ) (N : ℕ)
    (ω : Ω) : ℝ :=
  (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, h (τ x ω)

/-- **The missing multiparameter maximal inequality for anchored boxes.**  For every box shape
`c ≥ 0` and every `p > 1` there is `C` such that, for every bounded measurable `h`,
`∫⁻ ω, (sup_N |anchoredBoxAvg_N h ω - (∏ᵢ cᵢ) ∫ h|) ^ p ∂μ ≤ C ∫⁻ ω, |h ω - ∫ h| ^ p ∂μ`. -/
def AnchoredBoxMaximal (d : ℕ) (c : Fin d → ℝ) (p : ℝ) : Prop :=
  (∀ i, 0 ≤ c i) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω),
    (∀ z, MeasurePreserving (τ z) μ μ) →
    (∀ z w ω, τ (z + w) ω = τ z (τ w ω)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Ω → ℝ), Measurable h →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) →
      ∫⁻ ω, (⨆ N : ℕ,
          ENNReal.ofReal |anchoredBoxAvg h τ c N ω - (∏ i, c i) * ∫ ω, h ω ∂μ|) ^ p ∂μ ≤
        ENNReal.ofReal C *
          ∫⁻ ω, (ENNReal.ofReal |h ω - ∫ ω, h ω ∂μ|) ^ p ∂μ

end LatticeProb
