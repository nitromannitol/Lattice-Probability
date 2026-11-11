import Mathlib
import LatticeProb.LQG.LQGMeasureNonatomic

/-!
# The universal non-atomicity input, LP form

LP form of the HB statement `LQGMeasureNonatomicAll` (`HarmonicBalls/FirstPass/S11n/MeasureDecoder.lean:39`): for every
whole-plane GFF model `(Ω, P, hC, hcirc)` and every `γ, α₀`, the LQG measure has no atom at any point almost surely. It is the
universal form of the LP Proposition `LQGMeasureNonatomicLP` (`LatticeProb/LQG/LQGMeasureNonatomic.lean`, Fact 2.1 I of
Bou-Rabee-Gwynne, arXiv:2208.11795, p. 9).

PROVED from the LP forms of the literature inputs (hypotheses only): `WholePlaneLQGBallMassBoundsLP` (Ding-Gwynne 2020,
Lemma 3.8), `LQGMeasureCoordChangeLP` at `α₀ = 0` and `LQGMeasureExistenceLP` (`LatticeProb/LQG/LQGMeasureInputs.lean`). The HB
derivation is `HarmonicBalls.lqgMeasureNonatomicAll_of_inputs` (`FirstPass/Phase2/DerivedInputs15.lean:57`).
-/

universe u

namespace LatticeProb.LQG

open MeasureTheory

/-- LP form of `LQGMeasureNonatomicAll` (`HarmonicBalls/FirstPass/S11n/MeasureDecoder.lean:39`): the universal form of the
non-atomicity of `LQGMeasureNonatomicLP` for every whole-plane GFF model and every `γ, α₀`. -/
def LQGMeasureNonatomicAllLP : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomicLP P γ α₀ hC hcirc

/-- `LQGMeasureNonatomicAllLP` from the LP literature inputs (LP copy of `lqgMeasureNonatomicAll_of_inputs`). -/
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
