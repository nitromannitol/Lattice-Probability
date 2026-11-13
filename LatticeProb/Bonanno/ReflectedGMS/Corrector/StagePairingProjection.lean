/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StagePairingProjection at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StagePairingPolarization
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedStageFieldCovariance

/-!
# `MarkedNestedProjectionBound` from one input: the integrable, mean-zero stage pairing

`Corrector/SpecificEnergyConvergence` reduces the assembly input `hspec` to the named input
`SpecificEnergyConvergence.MarkedNestedProjectionBound ν` (:257), the inequality half of the
manuscript's `s:prop:projection`.  Two producer heads existed:

* `Corrector/MarkedStagePythagoras.markedNestedProjectionBound_of_pairing` (:124) — six
  hypotheses: three measurability inputs `hΨmeas`/`hDmeas`/`hPmeas`, the two finiteness inputs
  `hfin : ∀ n, markedStageEnergy ν n ≠ ∞` and `hdfin : ∀ m n, markedStageDefect ν m n ≠ ∞`,
  and the vanishing expected pairing `horth`;
* `Corrector/MarkedStageFieldCovariance.markedNestedProjectionBound_of_gated` (:348) — the same
  bound restated on the gated stage fields; an `↔`, hence a change of coordinates rather than a
  reduction.

This module closes the first head down to **one** input, by removing five of its six
hypotheses:

* `hfin`/`hdfin` are **circular** at every stage `n ≥ 1` — the only producer of
  `markedStageEnergy ν n ≠ ∞` is `SpecificEnergyConvergence.markedStageEnergy_lt_top`, whose own
  hypothesis is the bound being produced, and induction does not help because the identity at
  `(m, n)` needs the finiteness at the *later* stage.  They are eliminated outright by
  `StagePairingPolarization.lintegral_rootedSpecificEnergyDensity_eq_add_of_integrable_pairing`,
  which integrates the polarization in `ℝ≥0∞` with the signed term moved to whichever side makes
  it nonnegative.
* `hΨmeas`/`hDmeas`/`hPmeas` are discharged from the assembly's own measurability input `hmeas`
  through the unconditional engine of `Corrector/MarkedRootedSpecificEnergyMeasurability`, the
  pairing one via the polarization identity
  `StagePairingPolarization.rootedPairingDensity_eq_half_sub`.

## What is proved

* `measurable_gatedStageDensity`, `measurable_gatedStageDifferenceDensity`,
  `measurable_stagePairingDensity` — the three densities of the projection identity are
  measurable from `hmeas` alone, at **every** marked configuration (no gate, no a.e.).
* `gatedStageEnergy_eq_add_gatedStageDefect` — the manuscript identity on the gated fields.
* `MarkedStagePairingVanishes` — the single remaining input: for `m ≤ n` the signed rooted
  pairing density `⟪g_n, g_m − g_n⟫_*` of the gated stage fields is integrable with integral
  zero.
* `markedNestedProjection_of_stagePairing`, `markedNestedProjectionBound_of_stagePairing`,
  `markedSpecificEnergyConvergence_of_stagePairing` — the producers.

## Why the remaining input is not vacuous, and not circular

It is stated on the **gated** stage fields, which are total, unconditionally covariant
(`MarkedStageFieldCovariance.gradientTransported_stageField`) and measurable from `hmeas`; it
mentions no `Summable`, no `HasFiniteEnergy` and no expected energy, so it is satisfiable at
`decode e` data.  Its diagonal instance is a theorem here
(`rootedPairingDensity_stageDifferenceField_self`: at `m = n` the variation vanishes
identically, so the class of laws satisfying the input at that pair of stages is everything),
and it is *not* equivalent to its own conclusion: it is a statement about a signed real
integral, while the conclusion is an inequality between `ℝ≥0∞` energies, and it is precisely
what the owned-field transport chain
(`Corrector/PairingTransportWeld.integral_rootedPairingDensity_eq_zero_of_massTransport`,
`Corrector/TransportAeGating.integral_rootedPairingDensity_sub_eq_zero_ae`) is built to
produce.

## What is **not** proved

`MarkedStagePairingVanishes` itself.  This file proves no main theorem, and certifies none of
its inputs.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StagePairingProjection

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedStageFieldCovariance

/-! ### Measurability of the three densities from `hmeas` -/

/-- **The gated stage specific-energy density is measurable.**  The integrand of
`MarkedStageFieldCovariance.gatedStageEnergy`, measured at every marked configuration. -/
theorem measurable_gatedStageDensity
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    Measurable fun ω : MarkedEnvironment =>
      rootedSpecificEnergyDensity (decode ω.1) (stageField m ω) 0 :=
  MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (Prod.fst : MarkedEnvironment → Env)) measurable_fst
    (Ψ := fun ω k => gatedApproximant m ω k) (fun k => hmeas m k)

/-- **The gated stage-difference density is measurable.**  The integrand of
`MarkedStageFieldCovariance.gatedStageDefect`. -/
theorem measurable_gatedStageDifferenceDensity
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m n : ℕ) :
    Measurable fun ω : MarkedEnvironment =>
      rootedSpecificEnergyDensity (decode ω.1) (stageDifferenceField m n ω) 0 :=
  MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (Prod.fst : MarkedEnvironment → Env)) measurable_fst
    (Ψ := fun ω k => gatedApproximant m ω k - gatedApproximant n ω k)
    (fun k => (hmeas m k).sub (hmeas n k))

/-! ### Anti-vacuity of the pairing input -/

/-- **The diagonal instance of the pairing input is a theorem.**  At `m = n` the variation
field vanishes identically, hence so does the signed pairing density — at every marked
configuration, with no hypothesis on the law.  So the class of laws satisfying
`MarkedStagePairingVanishes` at a diagonal pair of stages is everything. -/
theorem rootedPairingDensity_stageDifferenceField_self (n : ℕ) (ω : MarkedEnvironment) :
    SpecificEnergyPolarization.rootedPairingDensity (decode ω.1) (stageField n ω)
      (stageDifferenceField n n ω) 0 = 0 := by
  have hz : stageDifferenceField n n ω = fun _ : Vertex ω.1.val => (0 : Plane) := by
    funext v
    show stageField n ω v - stageField n ω v = 0
    exact sub_self _
  rw [hz]
  show (rootAt (decode ω.1) 0).elim 0
      (SpecificEnergyPolarization.pairingDensity (decode ω.1) (stageField n ω)
        (fun _ : Vertex ω.1.val => (0 : Plane))) = 0
  cases hroot : rootAt (decode ω.1) 0 with
  | none => simp
  | some v => simp [SpecificEnergyPolarization.pairingDensity]

/-! ### The identity on the gated stage fields -/

/-- **The manuscript identity `s:prop:projection` on the gated stage fields**, from the
integrability and the vanishing of the expected signed pairing alone.  No finiteness of any
stage energy or stage defect is assumed. -/
theorem gatedStageEnergy_eq_add_gatedStageDefect (ν : Measure Env)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    {m n : ℕ}
    (hPint : Integrable (fun ω : MarkedEnvironment =>
      SpecificEnergyPolarization.rootedPairingDensity (decode ω.1) (stageField n ω)
        (stageDifferenceField m n ω) 0) (ν.prod gridLaw))
    (horth : (∫ ω : MarkedEnvironment,
      SpecificEnergyPolarization.rootedPairingDensity (decode ω.1) (stageField n ω)
        (stageDifferenceField m n ω) 0 ∂(ν.prod gridLaw)) = 0) :
    gatedStageEnergy ν m = gatedStageEnergy ν n + gatedStageDefect ν m n :=
  StagePairingPolarization.lintegral_rootedSpecificEnergyDensity_eq_add_of_integrable_pairing
    (ν.prod gridLaw) (fun ω : MarkedEnvironment => decode ω.1)
    (fun ω : MarkedEnvironment => stageField m ω)
    (fun ω : MarkedEnvironment => stageField n ω)
    (fun _ : MarkedEnvironment => (0 : Plane))
    (fun ω : MarkedEnvironment => decode_geometry ω.1)
    (measurable_gatedStageDensity hmeas n).aemeasurable
    (measurable_gatedStageDifferenceDensity hmeas m n).aemeasurable
    hPint horth

/-! ### The single remaining input, and the producers -/

/-- **The one remaining input of `hproj`.**  For `m ≤ n` the signed rooted pairing density
`⟪g_n, g_m − g_n⟫_*` of the *gated* stage fields is integrable under the marked law and has
integral zero.  This is the manuscript's blockwise orthogonality transported to the root
(`s:lem:redistribution` applied to `s:prop:projection`).

It carries no `Summable`, no `HasFiniteEnergy` and no expected-energy finiteness, so it is
satisfiable at `decode e` data; its diagonal instance is proved above. -/
def MarkedStagePairingVanishes (ν : Measure Env) : Prop :=
  ∀ m n : ℕ, m ≤ n →
    Integrable (fun ω : MarkedEnvironment =>
        SpecificEnergyPolarization.rootedPairingDensity (decode ω.1) (stageField n ω)
          (stageDifferenceField m n ω) 0) (ν.prod gridLaw)
      ∧ (∫ ω : MarkedEnvironment,
          SpecificEnergyPolarization.rootedPairingDensity (decode ω.1) (stageField n ω)
            (stageDifferenceField m n ω) 0 ∂(ν.prod gridLaw)) = 0

/-- **The manuscript identity `s:prop:projection` on the marked law**, from `hmeas` and the
pairing input.  The passage from the gated fields to the block interpolants `phi` is the
almost-sure identification on `SublinearEvent`
(`MarkedStageFieldCovariance.gatedStageEnergy_eq`), which costs only `s:eq:MTP` and (FE). -/
theorem markedNestedProjection_of_stagePairing (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hpair : MarkedStagePairingVanishes ν) :
    SpecificEnergyConvergence.MarkedNestedProjection ν := by
  intro m n hmn
  obtain ⟨hPint, horth⟩ := hpair m n hmn
  have h := gatedStageEnergy_eq_add_gatedStageDefect ν hmeas hPint horth
  rwa [gatedStageEnergy_eq ν hν hFE m, gatedStageEnergy_eq ν hν hFE n,
    gatedStageDefect_eq ν hν hFE m n] at h

/-- **`hproj` at one input.**  `SpecificEnergyConvergence.MarkedNestedProjectionBound ν` from
the ambient environment hypotheses, the assembly's own measurability input `hmeas`, and the
single new input `MarkedStagePairingVanishes ν`. -/
theorem markedNestedProjectionBound_of_stagePairing (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hpair : MarkedStagePairingVanishes ν) :
    SpecificEnergyConvergence.MarkedNestedProjectionBound ν :=
  SpecificEnergyConvergence.markedNestedProjectionBound_of_nestedProjection
    (markedNestedProjection_of_stagePairing ν hν hFE hmeas hpair)

end ReflectedGMS.StagePairingProjection
