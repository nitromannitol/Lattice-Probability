import Mathlib
import LatticeProb.LQG.LQGMeasureNonatomicOrigin
import LatticeProb.LQG.LQGMeasureNonatomicMassWholePlane
import LatticeProb.LQG.LQGMeasureNonatomicMassRescaled
import LatticeProb.LQG.LQGMeasureNonatomicMassTail
import LatticeProb.LQG.LQGMeasureNonatomicMassScaled
import LatticeProb.LQG.LQGMeasureNonatomicMassMixture
import LatticeProb.LQG.LQGMeasureInputs

/-!
# Non-atomicity of the singular LQG measure (chain statement)

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Fact 2.1 I, with the same binders and conclusion. It is PROVED here, not assumed: `lqgMeasureNonatomic_lp` takes the
forms of the literature inputs `WholePlaneLQGBallMassBoundsLP` (Ding and Gwynne 2020, Lemma 3.8), `LQGMeasureCoordChangeLP`
at `α₀ = 0` and `LQGMeasureExistenceLP` (module `LatticeProb.LQG.LQGMeasureInputs`) as hypotheses only. The argument
follows the non-atomicity argument of the source: the atom at `0` is removed by a strictly stronger insertion
(`ae_origin_nonatomic_of_stronger_existence`), and non-atomicity off `0` follows from the whole-plane multiscale ball-mass
bound and the Weyl identity. The whole-plane affine invariance and the mixture are proved results
(`wholePlaneGFFAffineInvariance_lp`, `wholePlaneGFFMixtureStep_lp`), not hypotheses.
-/

universe u

namespace LatticeProb.LQG

open MeasureTheory Filter Topology Set LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.LQGMeasureNonatomicOrigin (ae_origin_nonatomic_of_stronger_existence)
open LatticeProb.LQG.LQGMeasureNonatomicMass

-- Form of the literature input `LQGMeasureNonatomic` (Fact 2.1 I), with the same binders and conclusion; proved as
-- `lqgMeasureNonatomic_lp`.
/-- **Fact 2.1 I (Radon measure)**: a.s. `μ_h` is a non-atomic Radon measure. Radon (locally finite)
is part of `IsLQGMeasureOfField`; this Prop is the non-atomicity. Source: Bou-Rabee and Gwynne (arXiv:2208.11795),
Fact 2.1 I, where the non-atomicity is said to be immediate from the definition. The assertion holds simultaneously for all points; uniqueness of the locally
finite vague limit makes the choice of `μ` immaterial. Berestycki-Powell (arXiv:2404.16642v2), Theorems 2.1
and 3.2 (pp. 62 and 81), require transfer to this whole-plane singular field.
-/
def LQGMeasureNonatomicLP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0

/-- Non-atomicity of the LQG measure from the forms of the literature inputs. -/
theorem lqgMeasureNonatomic_lp
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBoundsLP P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChangeLP P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistenceLP P γ α hC hcirc) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomicLP P γ α hC hcirc := by
  intro Ω _ P γ α hC hcirc
  have hS : WholePlaneScaledBallMassStepLP.{u} :=
    wholePlaneScaledBallMassStep_of_uniform_lp (rescaledBallMassUniformStep_lp hDG hCC)
      circleAverageDyadicTailStep_lp
  intro hG hγ hγ2 hα μ hμ
  let β : ℝ := (α + lqgQ γ) / 2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβ : β < lqgQ γ := by dsimp [β]; linarith
  filter_upwards [ae_origin_nonatomic_of_stronger_existence P γ α β hγ hγ2 hαβ hβ
      hC hcirc (hE Ω P γ β hC hcirc) μ hG hμ,
    ae_singular_nonatomic_off_origin_of_scaledBallMass hS P γ α hγ hγ2 hα hC hcirc
      (hE Ω P γ 0 hC hcirc) μ hG hμ] with ω h0 hoff z
  by_cases hz : z = 0
  · simpa [hz] using h0
  · exact hoff z hz

end LatticeProb.LQG
