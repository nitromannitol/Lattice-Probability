/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.HarmonicCoordinateThreeInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicCoordinateFiveInputs
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SmallBlockResidualProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GeometricMassQuadraticProducer
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AuxiliaryGridMarkedSpaceProjection
import LatticeProb.Bonanno.ReflectedGMS.Spatial.CopyDifferenceThreeGridProjection

/-!
# The harmonic-coordinate reduction at **three** named inputs

`Corrector/HarmonicCoordinateFiveInputs.harmonicCoordinateConclusions_of_five_inputs` reduces the
harmonic-coordinate theorem to the five named inputs `hmeas, hproj, hmax, hcopies, hsub`.  Three
of those five have since been produced, in modules that had **no importers**, so no checked
statement carried the resulting count.  This file composes them.

## What is composed (all by application; no binder is restated)

| five-input binder | producer | residue |
|---|---|---|
| `hmax` — `StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν` | `Spatial/AuxiliaryGridMarkedSpaceProjection.markedStageDifferenceWeakMaximal_auxTwoGrid` | `hmeas` |
| `hsub` — `MarkedCentroidSublinearity ν ms` | `Spatial/AuxiliaryGridMarkedSpaceProjection.markedResidualWeakMaximal_auxTwoGrid` fed to `Corrector/HarmonicCoordinateResidualOnly.markedCentroidSublinearity_of_residualMaximal` | `hmeas` (+ `hharm`, `hspec`, both *produced inside* the assembly) |
| `hcopies` — `DifferenceFieldGridIndependent ν ms` | `Spatial/CopyDifferenceThreeGridProjection.differenceFieldGridIndependent_of_originEnergy_threeGrid` | `hmeas` and `hzero` |

## DISCHARGED vs REDUCED — stated exactly

* **DISCHARGED** (no residue at all beyond the manuscript's own `hν`, `hFE` and the assembly's
  `hmeas`): the entire marked-space producer for all three binders — `hchain`, `hdata`, `henv`,
  `hprojA`, `hmap`, `hshift`, `hdilate`, and for the copy lane also `hcov`, `hinv`.  Also
  discharged outright: `MarkedGeometricMassQuadratic` (inside
  `markedCentroidSublinearity_of_residualMaximal`), and `hgeom`, `hconv`, `hpatch`, `hharm`,
  `hspec`, which are produced from `hproj`, `hmax` and `hmeas` inside the five-input route.
* **REDUCED, not discharged**: `hmax` and the maximal input of `hsub` are reduced to `hmeas`;
  `hcopies` is reduced to `hmeas` together with `hzero`.

## `hsub` costs exactly one input, and it is `hmeas` — traced

`hsub = MarkedCentroidSublinearity ν ms` is produced by
`HarmonicCoordinateResidualOnly.markedCentroidSublinearity_of_residualMaximal` from
`hharm : MarkedHarmonicity ν ms`, `MarkedResidualWeakMaximal ν ms` and
`hspec : MarkedSpecificEnergyConvergence ν ms` (the `MarkedGeometricMassQuadratic` half of
`SmallBlockResidualProducer.markedCentroidSublinearity_of_weakMaximal` is discharged there from
`hν`/`hFE`).  Of those three, `markedResidualWeakMaximal_auxTwoGrid` supplies the second from
`hmeas`; the other two are **not** extra inputs here, because the five-input route already
manufactures them along its own subsequence: `hharm` from `hpatch` by
`MarkedRectangleOrthogonalityProducer.markedHarmonicity_of_patchConvergence`, and `hspec` from
`hproj`, `hmeas` and `hconv` by
`SpecificEnergyConvergence.markedSpecificEnergyConvergence_of_nestedProjection`.  That is why the
composition has to reproduce the five-input route's *body* rather than apply its statement: the
statement asks for `hsub` uniformly in `ms`, and `hharm`/`hspec` are available only at the
subsequence `hproj` produces.  Everything below is still application-style; no binder is inlined.

## Honest count: **three** named open inputs

`hmeas`, `hproj`, `hzero`.  (`hν : MassTransport ν` and `hFE : FiniteEnergyMoment ν` are the
manuscript's own environment hypotheses, `s:eq:MTP` and (FE), not open obligations.)

* `hmeas` — measurability of the gated approximants, the assembly's own input.
* `hproj` — `SpecificEnergyConvergence.MarkedNestedProjectionBound ν`.  Deliberately taken as a
  binder: a separate lane owns its reduction and is editing there, so nothing here depends on it.
* `hzero` — the manuscript's cross orthogonality in its integrability-free `ℝ≥0∞` form, the
  vanishing of the expected rooted specific-energy density at the origin of the difference of the
  two grid-copy potentials.  By
  `Corrector/CopyDifferenceInputReduction.integral_rootedPairing_diff_self_eq` this is the
  irreducible content of `hcopies`.

`hzero` is asked uniformly in the subsequence, exactly as the five-input theorem asks `hcopies`
and `hsub`; this is **no strengthening** relative to that head (indeed it is asked only for
strictly monotone `ms`).  `harmonicCoordinateConclusions_of_rate_and_originEnergy` below is the
fixed-`ms` variant that quantifies over nothing, at the price of carrying `hgeom` and `hspec` as
binders.

**This file proves no main theorem.**  Every statement here is an implication, and it certifies
none of its inputs: `hmeas`, `hproj` and `hzero` are open.
-/

-- Merged from `ReflectedGMS/Corrector/HarmonicCoordinateResidualOnly.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_HarmonicCoordinateResidualOnly

/-!
# `hsub` removed from the harmonic-coordinate reduction

`HarmonicCoordinateAssembly.harmonicCoordinateConclusions_of_named_inputs` carries ten open
inputs, of which `hsub` (`MarkedCentroidSublinearity`) is the **only** carrier of
non-degeneracy: the adversarial statement audit checked that the zero field satisfies
`GradientCovariant`, `NormalizedCovariant`, `RootNormalized`, `DiscreteHarmonicity` and
`FullRectangleOrthogonality`, and the representative-independent clause of
`SublinearCorrector` (`Environment/Potentials.lean:50-51`) is derived from `hsub`.

This module states the reduction with `hsub` gone.  It composes

* `Corrector/CentroidSublinearityFromResidual` and
  `Corrector/MarkedCentroidSublinearityProducer` — `hsub` from `s:eq:smallresidual`
  (`MarkedSmallBlockResidual`) and `s:eq:Wbound` in quadratic form
  (`MarkedGeometricMassQuadratic`);
* `Corrector/GeometricMassQuadraticProducer` — `MarkedGeometricMassQuadratic` **discharged**
  from `s:eq:MTP` and the finite (FE) moment alone;
* `Corrector/SmallBlockResidualProducer` — `MarkedSmallBlockResidual` from the manuscript's
  weak-`L¹` maximal inequality `s:eq:maximal` applied to the residual density
  (`MarkedResidualWeakMaximal`), together with `hspec`, an input the assembly already takes.

So `hsub` is replaced by exactly **one** new hypothesis, `MarkedResidualWeakMaximal`, and no
other input of the assembly changes.  That hypothesis is the project's own
`Spatial/SimilarityBlockAveraging.measure_ballMaximal_gt_le_similarity` read at the residual
density instead of the rooted (FE) density; what is missing to instantiate it is recorded in
the docstring of `Corrector/SmallBlockResidualProducer`.

**This file proves no main theorem.**  Its statements are implications with open hypotheses;
a conditional reduction certifies neither its inputs nor `HarmonicCoordinateMainTheorem`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.HarmonicCoordinateResidualOnly

open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients DyadicApproximation HarmonicMainStatement
open HarmonicCoordinateAssembly CentroidSublinearityFromResidual
open MarkedCentroidSublinearityProducer SmallBlockResidualProducer
open GeometricMassQuadraticProducer

/-- **`hsub` from one new input.**  The centroid half of `s:eq:sublinear` for the marked
limit, from full-rectangle minimality `hharm`, the weak-`L¹` maximal bound for the residual
density, the mean-residual convergence `hspec` the assembly already takes, and the
manuscript's own `s:eq:MTP` and finite (FE) moment. -/
theorem markedCentroidSublinearity_of_residualMaximal (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hharm : MarkedHarmonicity ν ms)
    (hmax : MarkedResidualWeakMaximal ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    MarkedCentroidSublinearity ν ms :=
  markedCentroidSublinearity_of_weakMaximal ν hν hFE ms hharm
    (markedGeometricMassQuadratic_of_massTransport ν hν hFE) hmax hspec

end ReflectedGMS.HarmonicCoordinateResidualOnly

end Merged_HarmonicCoordinateResidualOnly

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.HarmonicCoordinateThreeInputs

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open GridIndependenceDifferenceBridge

/-! ### The fixed-subsequence form: nothing is quantified -/

/-- **`hmax`, the maximal half of `hsub`, and the maximal half of `hcopies` discharged, at a
subsequence fixed in advance.**

Compared with
`Corrector/HarmonicCoordinateFiveInputs.harmonicCoordinateConclusions_of_rate_and_weakMaximal`,
whose six binders are `hgeom, hmax, hmeas, hcopies, hsub, hspec`, three are gone: `hmax` and
`hsub` entirely, and `hcopies` down to `hzero`.  The remaining named inputs are

`hgeom, hmeas, hspec, hzero`,

and `hgeom`/`hspec` are precisely what `hproj` produces in the quantified form below.  Nothing is
strengthened: every binder is asked at the one `ms` supplied. -/
theorem harmonicCoordinateConclusions_of_rate_and_originEnergy (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hgeom : ∀ j n : ℕ, ms j ≤ n →
      SpecificEnergyConvergence.markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j))
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hspec : MarkedSpecificEnergyConvergence ν ms)
    (hzero : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
        (fun u => firstPotential ms p u - secondPotential ms p u) 0
          ∂ν.prod (gridLaw.prod gridLaw)) = 0) :
    HarmonicCoordinateConclusions ν := by
  have hmax : StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν :=
    AuxiliaryGridMarkedSpace.markedStageDifferenceWeakMaximal_auxTwoGrid ν hν hFE hmeas
  have hconv : MarkedDifferencesConverge ν ms :=
    MarkedDifferenceIncrementsFromMaximal.markedDifferencesConverge_of_stageDifferenceWeakMaximal
      ν hν hFE ms hms hgeom hmax
  have hpatch : MarkedPatchConvergence ν ms :=
    StageDifferenceWeakMaximal.markedPatchConvergence_of_stageDifferenceWeakMaximal ν hν hFE
      ms hms hgeom hmax hconv
  have hharm : MarkedHarmonicity ν ms :=
    MarkedRectangleOrthogonalityProducer.markedHarmonicity_of_patchConvergence ν hν hFE ms hms
      hpatch
  have hsub : MarkedCentroidSublinearity ν ms :=
    HarmonicCoordinateResidualOnly.markedCentroidSublinearity_of_residualMaximal ν hν hFE ms
      hharm (AuxiliaryGridMarkedSpace.markedResidualWeakMaximal_auxTwoGrid ν hν hFE ms hmeas)
      hspec
  have hcopies : DifferenceFieldGridIndependent ν ms :=
    CopyDifferenceThreeGridSpace.differenceFieldGridIndependent_of_originEnergy_threeGrid
      ν hν hFE ms hmeas hzero
  exact HarmonicCoordinateFiveInputs.harmonicCoordinateConclusions_of_rate_and_weakMaximal ν hν
    hFE ms hms hgeom hmax hmeas hcopies hsub hspec

/-! ### The three-input reduction -/

end ReflectedGMS.HarmonicCoordinateThreeInputs
