/-
# The anchored-box ergodic theorem: the invariance identification

The library's box-iteration theorem (`LatticeProb/Prob/AkcogluKrengelAE/BoxTiling.lean`,
`exists_ae_tendsto_anchoredBox_with_integral`; branch `rectangle-ergodic-reduction`, commit
`567b92d`) gives, for a measure-preserving additive `ℤᵈ`-action `σ`, a bounded measurable `h` with
bound `M`, and `c ≥ 0`, a bounded measurable limit `G` with `∫G = ∫h` and, a.e.,
`N⁻ᵈ ∑_{x ∈ anchoredBox c N} h (σ x ω) → (∏ᵢ cᵢ) · G ω`.  `AnchoredBoxErgodic` wants the constant
`(∏ᵢ cᵢ) · ∫h`; the only missing content is identifying `G` with the mean, which splits into two
named steps:

* `AnchoredBoxLimitInvariant` — the **boundary-slab estimate**: for each fixed `z`, the anchored-box
  sum at `ω` and at `σ z ω` differ by the boundary layer of `∏ᵢ [0,N)` against `z + ∏ᵢ [0,N)`,
  whose relative size tends to `0`, so `G` is a.e. invariant under `σ`;
* `ErgodicConstantLimit` — an a.e.-invariant bounded function on an ergodic probability space is
  a.e. constant, so `G = ∫h` a.e.

Given the box-iteration statement plus both, `AnchoredBoxErgodic d` follows, and the library's
already-proved `RectangleErgodic_of_AnchoredBox` gives `RectangleErgodic`.  The box-iteration
statement is kept as the `Prop` `AnchoredBoxLimitExists` here so that this file depends only on
`RectangleErgodic` (the box-iteration module's build being out of sync on the shared checkout);
it is exactly the conclusion of `exists_ae_tendsto_anchoredBox_with_integral`.
-/
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The box-iteration statement (the conclusion of `exists_ae_tendsto_anchoredBox_with_integral`):
for a measure-preserving additive action, a bounded measurable `h`, and `c ≥ 0`, there is a bounded
measurable `G` with `∫G = ∫h` and a.e. convergence to `(∏ᵢ cᵢ) · G ω`. -/
def AnchoredBoxLimitExists (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Site d → Ω → Ω), (∀ z, MeasurePreserving (σ z) μ μ) →
    (∀ z w ω, σ (z + w) ω = σ z (σ w ω)) →
    ∀ (h : Ω → ℝ), Measurable h → ∀ {M : ℝ}, 0 ≤ M → (∀ x, |h x| ≤ M) →
    ∀ (c : Fin d → ℝ), (∀ i, 0 ≤ c i) →
      ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧ ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ ∧
        ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
            ∑ x ∈ anchoredBox c N, h (σ x ω)) atTop (𝓝 ((∏ i, c i) * G ω))

/-- **Boundary-slab invariance of the box limit.**  The limit `G` of the anchored-box averages is
almost surely invariant under the action: for each fixed `z` the anchored-box sum at `σ z ω`
differs from the one at `ω` by the boundary slab of `∏ᵢ [0,N)` against `z + ∏ᵢ [0,N)`, whose
normalised size tends to `0`, and the two limits are the same constant shifted. -/
def AnchoredBoxLimitInvariant (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Site d → Ω → Ω), (∀ z, MeasurePreserving (σ z) μ μ) →
    (∀ z w ω, σ (z + w) ω = σ z (σ w ω)) →
    ∀ (h : Ω → ℝ), Measurable h → ∀ {M : ℝ}, 0 ≤ M → (∀ x, |h x| ≤ M) →
    ∀ (c : Fin d → ℝ), (∀ i, 0 ≤ c i) →
    ∀ (G : Ω → ℝ), Measurable G → ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ →
      (∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ anchoredBox c N, h (σ x ω)) atTop (𝓝 ((∏ i, c i) * G ω))) →
      ∀ᵐ ω ∂μ, ∀ z : Site d, G (σ z ω) = G ω

/-- **The constant-limit step.**  On an ergodic probability space an a.e.-invariant bounded
function is a.e. constant; since `∫G = ∫h`, the box limit `G` equals the mean `∫h` a.e. -/
def ErgodicConstantLimit (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Site d → Ω → Ω), (∀ z, MeasurePreserving (σ z) μ μ) →
    (∀ z w ω, σ (z + w) ω = σ z (σ w ω)) →
    (∀ A : Set Ω, MeasurableSet A → (∀ z, σ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1) →
    ∀ (h : Ω → ℝ), Measurable h → ∀ {M : ℝ}, 0 ≤ M → (∀ x, |h x| ≤ M) →
    ∀ (c : Fin d → ℝ), (∀ i, 0 ≤ c i) →
    ∀ (G : Ω → ℝ), Measurable G → ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ →
      (∀ᵐ ω ∂μ, ∀ z : Site d, G (σ z ω) = G ω) →
      ∀ᵐ ω ∂μ, G ω = ∫ ω, h ω ∂μ

/-- **`AnchoredBoxErgodic` from the box iteration, the slab estimate, and ergodicity.** -/
theorem anchoredBoxErgodic_of_steps
    (hEx : AnchoredBoxLimitExists d) (hInv : AnchoredBoxLimitInvariant d)
    (hConst : ErgodicConstantLimit d) : AnchoredBoxErgodic d := by
  intro Ω _ μ _ σ hσ hσadd herg h hh hbdd c hc
  obtain ⟨M, hM, hb⟩ := hbdd
  obtain ⟨G, hGm, _hGb, hGint, hGconv⟩ := hEx μ σ hσ hσadd h hh hM hb c hc
  have hinv := hInv μ σ hσ hσadd h hh hM hb c hc G hGm hGint hGconv
  have hconst := hConst μ σ hσ hσadd herg h hh hM hb c hc G hGm hGint hinv
  filter_upwards [hGconv, hconst] with ω h1 h2
  rwa [h2] at h1

/-- **`RectangleErgodic` from the box iteration, the slab estimate, and ergodicity.** -/
theorem rectangleErgodic_of_steps
    (hEx : AnchoredBoxLimitExists d) (hInv : AnchoredBoxLimitInvariant d)
    (hConst : ErgodicConstantLimit d) : RectangleErgodic d :=
  RectangleErgodic_of_AnchoredBox (anchoredBoxErgodic_of_steps hEx hInv hConst)

#print axioms anchoredBoxErgodic_of_steps
#print axioms rectangleErgodic_of_steps

end LatticeProb
