import Mathlib
import LatticeProb.LQG.LQGMeasureNonatomic

/-!
# The universal non-atomicity statement

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Fact 2.1 I, in universal form: for every whole-plane GFF model `(Ω, P, hC, hcirc)` and every `γ, α₀`, the LQG measure has
no atom at any point almost surely. It is the universal form of `LQGMeasureNonatomicLP` (module
`LatticeProb.LQG.LQGMeasureNonatomic`; Fact 2.1 I of Bou-Rabee and Gwynne, arXiv:2208.11795, p. 9).

PROVED from the forms of the literature inputs (hypotheses only): `WholePlaneLQGBallMassBoundsLP` (Ding and Gwynne 2020,
Lemma 3.8), `LQGMeasureCoordChangeLP` at `α₀ = 0` and `LQGMeasureExistenceLP` (module `LatticeProb.LQG.LQGMeasureInputs`).
The universal form is derived from these inputs.
-/

universe u

namespace LatticeProb.LQG

open MeasureTheory

/-- The universal form of the non-atomicity of `LQGMeasureNonatomicLP`, for every whole-plane GFF model and every
`γ, α₀`. -/
def LQGMeasureNonatomicAllLP : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomicLP P γ α₀ hC hcirc

/-- `LQGMeasureNonatomicAllLP` from the literature inputs. -/
theorem lqgMeasureNonatomicAll_lp
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBoundsLP P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChangeLP P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistenceLP P γ α hC hcirc) :
    LQGMeasureNonatomicAllLP.{u} := by
  intro γ α₀ Ω _ P hC hcirc
  exact lqgMeasureNonatomic_lp hDG hCC hE Ω P γ α₀ hC hcirc

end LatticeProb.LQG
