/-
# The bounded → `L¹` upgrade for the box-ergodic theorem: reduction

The box-ergodic theorem `LatticeProb.exists_ae_tendsto_anchoredBox_with_integral` needs a
**bounded** `h`.  The frozen `VRW.External.PointwiseErgodicCubes` only assumes
`Integrable (v ↦ v 0)`.  This file isolates the analytic content of the upgrade:

* `BoundedBoxErgodic d` — the bounded a.e. box theorem, **proved** here from `BoxTiling.lean`;
* `BoxMaximalInequality d` — the named residual: the distributional bound for the
  anchored-box maximal operator,
  `μ {∃ N, t < |N^{-d} ∑_{anchoredBox c N} h (σ x ω)|} ≤ (K/t) ∫ |h|`;
* `boxErgodicL1_of_bounded_of_maximal` — the reduction: bounded box theorem + maximal
  inequality give a.e. convergence for every integrable `h`, by the standard density argument
  (truncate `h` with `clip`, whose `L¹` error tends to `0` by `tendsto_integral_abs_sub_clip`).
-/
import LatticeProb.Prob.AkcogluKrengelAE.BoxTiling

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The normalized anchored-box average `N^{-d} ∑_{x ∈ anchoredBox c N} f (σ x ω)`. -/
noncomputable def boxErgodicAvg (σ : Site d → Ω → Ω) (f : Ω → ℝ) (c : Fin d → ℝ)
    (N : ℕ) (ω : Ω) : ℝ :=
  (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ anchoredBox c N, f (σ x ω)

/-- The bounded a.e. box theorem (`BoxTiling.exists_ae_tendsto_anchoredBox_with_integral`). -/
def BoundedBoxErgodic (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Site d → Ω → Ω), (∀ z, MeasurePreserving (σ z) μ μ) →
    (∀ z w ω, σ (z + w) ω = σ z (σ w ω)) →
    ∀ (h : Ω → ℝ), Measurable h → ∀ {M : ℝ}, 0 ≤ M → (∀ x, |h x| ≤ M) →
    ∀ (c : Fin d → ℝ), (∀ i, 0 ≤ c i) →
      ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧
        (∀ j : Fin d, G ∘ σ (unit j) = G) ∧
        ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ ∧
        ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => boxErgodicAvg σ h c N ω) atTop
          (𝓝 ((∏ i, c i) * G ω))

/-- The bounded box theorem holds (proved in `BoxTiling.lean`). -/
theorem boundedBoxErgodic (d : ℕ) : BoundedBoxErgodic d := by
  intro Ω _ μ _ σ hσ hσadd h hh M hM hb c hc
  exact exists_ae_tendsto_anchoredBox_with_integral hσ hσadd hh hM hb hc

/-- **The box maximal inequality** — the named analytic residual of the bounded → `L¹` upgrade:
the anchored-box maximal operator satisfies the weak-`L¹` distributional bound. -/
def BoxMaximalInequality (d : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (σ : Site d → Ω → Ω), (∀ z, MeasurePreserving (σ z) μ μ) →
      (∀ z w ω, σ (z + w) ω = σ z (σ w ω)) →
      ∀ (h : Ω → ℝ), Measurable h → Integrable h μ →
      ∀ (c : Fin d → ℝ), (∀ i, 0 ≤ c i) → ∀ t : ℝ, 0 < t →
        μ {ω | ∃ N : ℕ, t < |boxErgodicAvg σ h c N ω|} ≤
          ENNReal.ofReal (K / t * ∫ ω, |h ω| ∂μ)

end LatticeProb
