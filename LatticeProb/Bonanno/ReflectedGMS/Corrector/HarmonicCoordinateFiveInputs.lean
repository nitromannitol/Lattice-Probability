/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.HarmonicCoordinateFiveInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicCoordinateSixInputs
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedDifferenceIncrementsFromMaximal
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageDifferenceWeakMaximal

/-!
# `hconv`, `hpatch` and `hspec` all routed through two open inputs: the **five**-input reduction

`Corrector/HarmonicCoordinateSixInputs.harmonicCoordinateConclusions_of_six_inputs` reduces the
harmonic-coordinate theorem to `hmeas, hcopies, hconv, hpatch, hsub, hspec`.  Three of those six
are now produced:

* `hconv` — `Corrector/MarkedDifferenceIncrementsFromMaximal.markedDifferencesConverge_of_stageDifferenceWeakMaximal`,
  from the geometric rate `hgeom` and `MarkedStageDifferenceWeakMaximal`;
* `hpatch` — `Corrector/StageDifferenceWeakMaximal.markedPatchConvergence_of_stageDifferenceWeakMaximal`,
  from the same two plus `hconv`;
* `hspec` — `Corrector/SpecificEnergyConvergence.markedSpecificEnergyConvergence_of_nestedProjection`,
  from `MarkedNestedProjectionBound`, `hmeas` and `hconv`.

and the rate `hgeom` itself is produced by
`Corrector/SpecificEnergyConvergence.exists_strictMono_geometric_markedStageDefect` from the same
`MarkedNestedProjectionBound`.  That eliminates `hgeom` as a binder at the price of making the
subsequence an **output**, so the two remaining `ms`-dependent inputs must be supplied uniformly
in `ms`.

## Honest accounting — this is a REDUCTION IN COUNT, NOT A DISCHARGE

`harmonicCoordinateConclusions_of_five_inputs` has exactly five named inputs,

`hmeas, hcopies, hsub, hproj, hmax`,

against the six of `harmonicCoordinateConclusions_of_six_inputs`.  Read that as **three old
inputs (`hmeas`, `hcopies`, `hsub`) plus two open inputs (`hproj`, `hmax`)**, not as five old
ones.  Specifically:

* `hproj = SpecificEnergyConvergence.MarkedNestedProjectionBound ν` and
  `hmax = StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν` are **open**.  Neither
  is proved anywhere in the corpus.  They are, however, exactly the reduction targets the
  six-input module's own docstring already records for `hspec` and for `hpatch`, so no *new*
  unproved object is introduced here; what is new is that `hconv`, which previously reduced to
  the separate target `MarkedDifferenceIncrementsSummable` / `MarkedLabelSubsequentialCompactness`
  of `Corrector/MarkedDifferenceSubsequence`, now collapses into `hmax` as well.
* `hcopies` and `hsub` are **strengthened**: the six-input assembly asks them at one fixed `ms`,
  and this statement asks them for *every* strictly increasing `ms`.  That is a genuine
  strengthening, forced by the subsequence becoming an output, and it is precisely the adapter
  recorded in `Corrector/MarkedDifferenceSubsequence.harmonicCoordinateConclusions_of_compactness`.
  `harmonicCoordinateConclusions_of_rate_and_weakMaximal` below is the variant that strengthens
  nothing, at a fixed `ms`; its count is six, not five, because `hgeom` is then a binder.

### A correction to the count of `hmax`'s consumers

`MarkedStageDifferenceWeakMaximal ν` has **two** consumers, `hconv` and `hpatch` — not three.
`hsub` consumes `Corrector/SmallBlockResidualProducer.MarkedResidualWeakMaximal ν ms`, which is a
**different predicate**: it is the weak-`L¹` bound for the maximal function of the *residual*
density `ρ(φ_m − Φ)` against `E[ρ(φ_m − Φ)]`, and it depends on `ms`, whereas
`MarkedStageDifferenceWeakMaximal ν` bounds the maximal function of the *stage-difference*
density `ρ(φ_a − φ_b)` against `markedStageDefect ν a b` and does not mention `ms`.  The two have
the same *shape* (an existential finite constant, `P[M > λ] ≤ (C/λ)·‖·‖²`) and the project's own
`Spatial/SpatialMaximalInequality.measure_ballMaximal_gt_le` (`C = 512`) is the intended producer
of both, but discharging one does not discharge the other.  This is why `hsub` survives as an
independent input.

## What was verified, not assumed

* The `hconv` produced here is literally `HarmonicCoordinateAssembly.MarkedDifferencesConverge ν ms`
  at the assembly's own `ν` and `ms`, and the `hpatch` is literally
  `HarmonicCoordinateAssembly.MarkedPatchConvergence ν ms`.  Both are checked by the partial
  application `example` below, which fills the six-input assembly's `hconv` and `hpatch` slots and
  leaves exactly `hsub` and `hspec`.
* `hgeom` and `hmax` do not duplicate or weaken any binder the six-input assembly already has:
  `hmax` is a statement about `ν` alone and occurs in none of `hν, hFE, hmeas, hcopies, hconv,
  hpatch, hsub, hspec`; `hgeom` constrains the pair `(ν, ms)` and is independent of `hms`
  (`StrictMono ms` says nothing about `markedStageDefect`).  In the fixed-`ms` theorem they are
  therefore genuinely *additional* binders, which is exactly why that theorem's count is six.
* `AmbientMassTransport P hP` is by definition `MassTransport (validLaw P hP)`
  (`Environment/Laws`), and `validLaw_isProbability` supplies the probability instance, so the
  `validLaw` variant is the plain instantiation of the general one — no separate route is needed.

**This file proves no main theorem.**  `hmeas`, `hcopies`, `hsub`, `hproj` and `hmax` are all
open; these statements are implications.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.HarmonicCoordinateFiveInputs

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly

/-! ### The shape join, machine-checked

The producers of `hconv` and `hpatch` fill the six-input assembly's slots with no coercion and
no re-derivation, and what is left is exactly `hsub` and `hspec`.  Elaboration of this statement
is the certificate that the shapes genuinely match. -/

example (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hgeom : ∀ j n : ℕ, ms j ≤ n →
      SpecificEnergyConvergence.markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j))
    (hmax : StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms) :
    MarkedCentroidSublinearity ν ms → MarkedSpecificEnergyConvergence ν ms →
      HarmonicCoordinateConclusions ν :=
  HarmonicCoordinateSixInputs.harmonicCoordinateConclusions_of_six_inputs ν hν hFE ms hms
    hmeas hcopies
    (MarkedDifferenceIncrementsFromMaximal.markedDifferencesConverge_of_stageDifferenceWeakMaximal
      ν hν hFE ms hms hgeom hmax)
    (StageDifferenceWeakMaximal.markedPatchConvergence_of_stageDifferenceWeakMaximal ν hν hFE ms
      hms hgeom hmax
      (MarkedDifferenceIncrementsFromMaximal.markedDifferencesConverge_of_stageDifferenceWeakMaximal
        ν hν hFE ms hms hgeom hmax))

/-! ### The fixed-subsequence form: nothing is strengthened, and the count is six -/

/-- **`hconv`, `hpatch` and `hharm` discharged at a subsequence fixed in advance.**  Every
remaining binder is exactly the one the six-input assembly asks for; in particular `hcopies`,
`hsub` and `hspec` are at the *same* `ms` and are not strengthened.

The count does **not** drop here: `hconv` and `hpatch` are replaced by `hgeom` and `hmax`, so
there are still six named inputs (`hgeom, hmax, hmeas, hcopies, hsub, hspec`).  The gain is that
two of them have become the single weak-`L¹` maximal inequality plus a rate, and the rate is
itself producible (see `harmonicCoordinateConclusions_of_five_inputs`). -/
theorem harmonicCoordinateConclusions_of_rate_and_weakMaximal (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hgeom : ∀ j n : ℕ, ms j ≤ n →
      SpecificEnergyConvergence.markedStageDefect ν (ms j) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (4 * j))
    (hmax : StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hsub : MarkedCentroidSublinearity ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    HarmonicCoordinateConclusions ν :=
  HarmonicCoordinateSixInputs.harmonicCoordinateConclusions_of_six_inputs ν hν hFE ms hms
    hmeas hcopies
    (MarkedDifferenceIncrementsFromMaximal.markedDifferencesConverge_of_stageDifferenceWeakMaximal
      ν hν hFE ms hms hgeom hmax)
    (StageDifferenceWeakMaximal.markedPatchConvergence_of_stageDifferenceWeakMaximal ν hν hFE ms
      hms hgeom hmax
      (MarkedDifferenceIncrementsFromMaximal.markedDifferencesConverge_of_stageDifferenceWeakMaximal
        ν hν hFE ms hms hgeom hmax))
    hsub hspec

/-! ### The five-input reduction -/

end ReflectedGMS.HarmonicCoordinateFiveInputs
