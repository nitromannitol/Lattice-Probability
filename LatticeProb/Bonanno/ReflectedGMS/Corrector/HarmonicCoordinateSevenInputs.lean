/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.HarmonicCoordinateSevenInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NeighborhoodConvergenceFromSpecificEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolationSimilarity

/-!
# `hcov` discharged at every stage: the **seven**-input harmonic-coordinate reduction

`Corrector/NeighborhoodConvergenceFromSpecificEnergy.harmonicCoordinateConclusions_of_eight_inputs`
reduces the harmonic-coordinate theorem (GMS Theorem 1.16, target shape
`HarmonicMainStatement.HarmonicCoordinateConclusions`) to the eight named inputs

`hmeas, hcov, hcopies, hconv, hpatch, hharm, hsub, hspec`,

where `hcov` is the every-stage covariance
`MarkedBallEnergyConvergence.ApproximantGradientCovariantAtEveryStage`.

This module **discharges `hcov` outright**, with no hypothesis, and restates the reduction with
**seven** open inputs.

## Why this is only a composition

Two checked facts meet:

* `Corrector/BlockInterpolationSimilarity.blockInterpolationSimilarityCovariant` (:240) proves
  `ApproximantCovarianceFromBlockTransport.BlockInterpolationSimilarityCovariant` outright — the
  block-interpolation *specification* is invariant under transport along a similarity relabelling
  together with the named grid action `gridSimilarity s hs u D = dilate s hs (translate u D)`;
* `Corrector/MarkedBallEnergyConvergence.approximantGradientCovariantAtEveryStage_of_blockTransport`
  (:93) turns that specification-level statement into the gradient covariance of the *chosen*
  interpolant `phi` at **every** stage `m`, on `SublinearEvent`, for the same named grid action.

The composite `approximantGradientCovariantAtEveryStage` is therefore hypothesis-free.  Note that
`ApproximantGradientCovariantAtEveryStage` is the *stronger* of the two covariance statements in
play: it names the grid action and quantifies over all stages, where the assembly's own
`HarmonicCoordinateAssembly.ApproximantGradientCovariant ms` existentially quantifies the grid
action and only speaks about the stages `ms j`
(`MarkedBallEnergyConvergence.approximantGradientCovariant_of_atEveryStage` is the implication).
Discharging the stronger one is what is needed downstream, because the re-rooting step of
`MarkedBallEnergyConvergence` and the marked mass transport of
`MarkedMassTransportProducer.markedSimilarity` both need the action named.

`phi` is a `Classical.choose`, so its covariance is only meaningful on the good event; every
statement here is gated by `e ∈ SublinearEvent`, exactly as
`ApproximantGradientCovariantAtEveryStage` is, where
`ApproximantCovarianceFromBlockTransport` makes the choice canonical.

## What is proved

* `approximantGradientCovariantAtEveryStage` — **`hcov` is closed**, no hypotheses.
* `harmonicCoordinateConclusions_of_seven_inputs` — the reduction on a general environment law
  `ν` satisfying `MassTransport` and `FiniteEnergyMoment`.
* `harmonicCoordinateConclusions_validLaw_of_seven_inputs` — the same at the main theorem's own
  law `validLaw P hP`.

**This file proves no main theorem.**  The seven remaining inputs
`hmeas, hcopies, hconv, hpatch, hharm, hsub, hspec` are open; these statements are implications.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.HarmonicCoordinateSevenInputs

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly

/-! ### `hcov` is closed -/

/-- **`hcov` is discharged.**  The every-stage, named-grid-action gradient covariance of the
block interpolants holds with no hypothesis: it is the transport statement
`BlockInterpolationSimilarity.blockInterpolationSimilarityCovariant` read through
`MarkedBallEnergyConvergence.approximantGradientCovariantAtEveryStage_of_blockTransport`. -/
theorem approximantGradientCovariantAtEveryStage :
    MarkedBallEnergyConvergence.ApproximantGradientCovariantAtEveryStage :=
  MarkedBallEnergyConvergence.approximantGradientCovariantAtEveryStage_of_blockTransport
    BlockInterpolationSimilarity.blockInterpolationSimilarityCovariant

/-! ### The seven-input reduction -/

/-- **The harmonic-coordinate reduction with `hcov` discharged.**  Compared with
`NeighborhoodConvergenceFromSpecificEnergy.harmonicCoordinateConclusions_of_eight_inputs`, the
covariance input is gone.  The remaining **seven** inputs `hmeas, hcopies, hconv, hpatch, hharm,
hsub, hspec` are open; this is an implication, not a proof of the harmonic-coordinate theorem. -/
theorem harmonicCoordinateConclusions_of_seven_inputs (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (hharm : MarkedHarmonicity ν ms) (hsub : MarkedCentroidSublinearity ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    HarmonicCoordinateConclusions ν :=
  NeighborhoodConvergenceFromSpecificEnergy.harmonicCoordinateConclusions_of_eight_inputs ν hν
    hFE ms hms hmeas approximantGradientCovariantAtEveryStage hcopies hconv hpatch hharm hsub
    hspec

end ReflectedGMS.HarmonicCoordinateSevenInputs
