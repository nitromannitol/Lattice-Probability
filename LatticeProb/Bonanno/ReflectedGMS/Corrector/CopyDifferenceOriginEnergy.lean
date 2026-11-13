/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.CopyDifferenceOriginEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CopyDifferenceInputReduction

/-!
# `hcopies` from **two** inputs, and the consistency of that pair

`Corrector/GridIndependenceDifferenceBridge` reduces `hcopies` to ten inputs and
`Corrector/CopyDifferenceInputReduction` collapses those to three.  The count is really **two**:
the whole cross-orthogonality block exists only to produce the single `ℝ≥0∞` statement

  `hzero : E[ ρ_{θ¹ − θ²}(0) ] = 0`

(the expected rooted specific-energy density of the difference of the two grid-copy potentials at
the origin), which together with the maximal input `CopyDifferenceWeakMaximal` already gives
`hcopies` through the bridge's own `differenceFieldGridIndependent_of_ae_disk` and
`ae_disk_eq_zero_of_weakMaximal`.

`differenceFieldGridIndependent_of_originEnergy` records that two-input form.  Its advantage over
the three-input form is not only the count: `hzero` is an `ℝ≥0∞` statement, so it carries **no
integrability side condition at all**, whereas the Bochner route must assume `hi`.

## The routes, and how they relate

* `originEnergy_eq_zero_of_cross_orthogonality` — the Bochner route: `hi` and `horth` of
  `Corrector/CopyDifferenceInputReduction.differenceFieldGridIndependent_of_cross_orthogonality`
  give `hzero`.  So the three-input theorem factors through the two-input one, and the ten-input
  bridge factors through the three-input one.  Nothing in this chain is circular: each step only
  discards hypotheses that the pointwise polarization identity or the grid swap already supplies.
* Any other proof of `hzero` — for instance one that never leaves `ℝ≥0∞` — plugs into
  `differenceFieldGridIndependent_of_originEnergy` directly.

## Anti-vacuity

The pair `(hzero, hmax)` is **consistent**: `originEnergy_eq_zero_of_ae_eq` and
`copyDifferenceWeakMaximal_of_ae_eq` prove both of them, with the explicit constant `C = 1`, from
the almost-sure equality of the two grid-copy potentials.  So neither hypothesis is
self-contradictory and neither is `⊥` in disguise — the failure mode of
`Limit/RootBlockGridProbability`'s `hdata`, whose hypothesis was unsatisfiable at the actual data,
does not occur here.

**This witness is deliberately reported as weak, and the reason is worth recording.**  It
establishes consistency only in the situation the conclusion itself describes.  That is not an
artefact of these two statements: by
`Corrector/CopyDifferenceInputReduction.integral_rootedPairing_diff_self_eq` and the pointwise
nonnegativity of the self-pairing, `hzero` *is* the vanishing of the expected specific energy of
`θ¹ − θ²`, which is the entire mathematical content of the origin step.  Any reduction of
`hcopies` along this route therefore has a hypothesis that is equivalent to the difficult half of
the conclusion; the real work is the manuscript's cross orthogonality, and no amount of further
bookkeeping will remove it.  What the reduction *does* buy is that a prospective proof now has a
single, integrability-free target.

**This file proves no main theorem.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.CopyDifferenceOriginEnergy

open Code DyadicApproximation RootDensities HarmonicMainStatement EnvironmentLaws
open HarmonicLawIngredients
open MarkedLimitingCoordinateMeasurability HarmonicCoordinateAssembly GridIndependenceCoupling
open GridIndependenceDifferenceBridge CopyDifferenceInputReduction

/-! ### The specific-energy density of a vanishing field -/

/-! ### The two-input reduction -/

/-- **`hcopies` from two inputs.**  The expected rooted specific-energy density of the difference
of the two grid-copy potentials at the origin vanishes, and the weak-`L¹` maximal inequality
holds.  No integrability hypothesis occurs: both inputs are `ℝ≥0∞` statements. -/
theorem differenceFieldGridIndependent_of_originEnergy (ν : Measure Env) (ms : ℕ → ℕ)
    (hzero : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
        (fun u => firstPotential ms p u - secondPotential ms p u) 0
          ∂ν.prod (gridLaw.prod gridLaw)) = 0)
    (hmax : CopyDifferenceWeakMaximal ν ms) :
    DifferenceFieldGridIndependent ν ms :=
  differenceFieldGridIndependent_of_ae_disk ν ms
    (ae_disk_eq_zero_of_weakMaximal (ν.prod (gridLaw.prod gridLaw))
      (fun q u => firstPotential ms q u - secondPotential ms q u) hzero hmax)

/-! ### The Bochner route factors through it -/

/-- **`hzero` from the single cross orthogonality relation and its integrability.**  This is the
content of `Corrector/CopyDifferenceInputReduction.differenceFieldGridIndependent_of_cross_orthogonality`
isolated from the maximal step: the three-input reduction is exactly the two-input one composed
with this. -/
theorem originEnergy_eq_zero_of_cross_orthogonality (ν : Measure Env) [SFinite ν] (ms : ℕ → ℕ)
    (hi : Integrable (rootedPairing (firstPotential ms)
      fun q u => secondPotential ms q u - firstPotential ms q u)
      (ν.prod (gridLaw.prod gridLaw)))
    (horth : (∫ p, rootedPairing (firstPotential ms)
      (fun q u => secondPotential ms q u - firstPotential ms q u) p
        ∂ν.prod (gridLaw.prod gridLaw)) = 0) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
      (fun u => firstPotential ms p u - secondPotential ms p u) 0
        ∂ν.prod (gridLaw.prod gridLaw)) = 0 := by
  have hi₃ := integrable_secondCross_of_first ν ms hi
  have hfun₁ : (rootedPairing (firstPotential ms)
      fun q u => firstPotential ms q u - firstPotential ms q u)
      = fun _ : CoupledSpace => (0 : ℝ) :=
    funext fun p => rootedPairing_self_sub _ _ p
  have hfun₄ : (rootedPairing (secondPotential ms)
      fun q u => firstPotential ms q u - firstPotential ms q u)
      = fun _ : CoupledSpace => (0 : ℝ) :=
    funext fun p => rootedPairing_self_sub _ _ p
  have hi₁ : Integrable (rootedPairing (firstPotential ms)
      fun q u => firstPotential ms q u - firstPotential ms q u)
      (ν.prod (gridLaw.prod gridLaw)) := by
    rw [hfun₁]; exact integrable_zero _ _ _
  have hi₄ : Integrable (rootedPairing (secondPotential ms)
      fun q u => firstPotential ms q u - firstPotential ms q u)
      (ν.prod (gridLaw.prod gridLaw)) := by
    rw [hfun₄]; exact integrable_zero _ _ _
  have hint := integrable_rootedPairing_diff_self (ν.prod (gridLaw.prod gridLaw))
    (firstPotential ms) (firstPotential ms) (secondPotential ms) hi₁ hi hi₃ hi₄
  have hsq : (∫ p, rootedPairing (fun q u => firstPotential ms q u - secondPotential ms q u)
      (fun q u => firstPotential ms q u - secondPotential ms q u) p
        ∂ν.prod (gridLaw.prod gridLaw)) = 0 := by
    rw [integral_rootedPairing_diff_self_eq ν ms hi, horth, mul_zero]
  exact lintegral_rootedSpecificEnergyDensity_origin_eq_zero (ν.prod (gridLaw.prod gridLaw))
    (fun q u => firstPotential ms q u - secondPotential ms q u)
    (ae_rootedPairing_self_eq_zero (ν.prod (gridLaw.prod gridLaw))
      (fun q u => firstPotential ms q u - secondPotential ms q u) hint hsq)

/-! ### Consistency of the two-input pair -/

/-! ### The weld to the six-input assembly, machine-checked -/

example (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hzero : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
        (fun u => firstPotential ms p u - secondPotential ms p u) 0
          ∂ν.prod (gridLaw.prod gridLaw)) = 0)
    (hmax : CopyDifferenceWeakMaximal ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms) :
    MarkedCentroidSublinearity ν ms → MarkedSpecificEnergyConvergence ν ms →
      HarmonicCoordinateConclusions ν :=
  HarmonicCoordinateSixInputs.harmonicCoordinateConclusions_of_six_inputs ν hν hFE ms hms hmeas
    (differenceFieldGridIndependent_of_originEnergy ν ms hzero hmax) hconv hpatch

end ReflectedGMS.CopyDifferenceOriginEnergy
