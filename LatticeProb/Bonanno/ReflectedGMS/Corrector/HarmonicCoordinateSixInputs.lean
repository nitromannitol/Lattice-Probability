/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.HarmonicCoordinateSixInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicCoordinateSevenInputs
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRectangleOrthogonalityProducer

/-!
# `hcov` and `hharm` both discharged: the **six**-input harmonic-coordinate reduction

`Corrector/HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs`
reduces the harmonic-coordinate theorem to the seven named inputs

`hmeas, hcopies, hconv, hpatch, hharm, hsub, hspec`.

`Corrector/MarkedRectangleOrthogonalityProducer.markedHarmonicity_of_patchConvergence` proves
`hharm = HarmonicCoordinateAssembly.MarkedHarmonicity ν ms` from `hν`, `hFE`, `hms` and
`hpatch`.  **Every one of those four is already a binder of the seven-input assembly**, so the
composition deletes `hharm` without adding anything: the remaining inputs are the **six**

`hmeas, hcopies, hconv, hpatch, hsub, hspec`.

That "no new hypothesis" claim is the anti-vacuity guarantee of this module, and it is
machine-checked twice: by the partial application `example` below, which fills the consumer's
`hharm` slot with the producer and leaves only `hsub` and `hspec` to be supplied, and by the
two theorems themselves.

**This file proves no main theorem.**  The six remaining inputs are open; these statements are
implications.

## Where the six now stand

* `hmeas` → `IsBlockInterpolantSelection` (`Corrector/GatedApproximantMeasurability`);
* `hcopies` → cross orthogonality and `CopyDifferenceWeakMaximal`
  (`Corrector/GridIndependenceDifferenceBridge`);
* `hconv` → `MarkedDifferenceIncrementsSummable` (`Corrector/MarkedDifferenceSubsequence`);
* `hpatch` → `MarkedStageDifferenceWeakMaximal` together with `hconv`
  (`Corrector/StageDifferenceWeakMaximal`), which does not lower the count on its own but
  replaces `hpatch` by a weak-maximal statement of the same shape as the two below;
* `hsub` → `MarkedResidualWeakMaximal` (`Corrector/HarmonicCoordinateResidualOnly`);
* `hspec` → `MarkedNestedProjectionBound` (`Corrector/SpecificEnergyConvergence`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.HarmonicCoordinateSixInputs

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly

/-! ### The shape join, machine-checked

The producer fills the consumer's `hharm` slot with no coercion, no re-derivation and no
hypothesis that the consumer does not already bind: this partial application elaborates, and
what is left is exactly `hsub` and `hspec`. -/

example (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms) :
    MarkedCentroidSublinearity ν ms → MarkedSpecificEnergyConvergence ν ms →
      HarmonicCoordinateConclusions ν :=
  HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs ν hν hFE ms hms
    hmeas hcopies hconv hpatch
    (MarkedRectangleOrthogonalityProducer.markedHarmonicity_of_patchConvergence ν hν hFE ms hms
      hpatch)

/-! ### The six-input reduction -/

/-- **The harmonic-coordinate reduction with `hcov` and `hharm` both discharged.**  Compared
with `HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs`, the
harmonicity input is gone; nothing has been added, because the producer of `hharm` consumes
only `hν`, `hFE`, `hms` and `hpatch`, all of which this statement already binds.  The
remaining **six** inputs `hmeas, hcopies, hconv, hpatch, hsub, hspec` are open; this is an
implication, not a proof of the harmonic-coordinate theorem. -/
theorem harmonicCoordinateConclusions_of_six_inputs (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (hsub : MarkedCentroidSublinearity ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    HarmonicCoordinateConclusions ν :=
  HarmonicCoordinateSevenInputs.harmonicCoordinateConclusions_of_seven_inputs ν hν hFE ms hms
    hmeas hcopies hconv hpatch
    (MarkedRectangleOrthogonalityProducer.markedHarmonicity_of_patchConvergence ν hν hFE ms hms
      hpatch)
    hsub hspec

end ReflectedGMS.HarmonicCoordinateSixInputs
