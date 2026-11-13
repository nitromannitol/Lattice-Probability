/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.CopyDifferenceInputReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GridIndependenceDifferenceBridge
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicCoordinateSixInputs

/-!
# `hcopies` from **three** inputs instead of ten

`Corrector/GridIndependenceDifferenceBridge.differenceFieldGridIndependent_of_orthogonality`
reduces `hcopies = HarmonicCoordinateAssembly.DifferenceFieldGridIndependent ν ms` to **ten**
open inputs: the four cross specific-orthogonality relations `h₁ … h₄` against an arbitrary
reference field `g₀`, their four integrability conditions `hi₁ … hi₄`, the integrability `hint`
of the self-pairing of the difference, and the weak-`L¹` maximal inequality
`CopyDifferenceWeakMaximal`.

This module cuts that list to **three** — one integrability condition, one orthogonality
relation and the unchanged maximal input — by three observations, none of which touches the
mathematics of the route:

1. **`hint` is free.**  `GridIndependenceCoupling.rootedPairing_sub_self` is a *pointwise*
   identity, valid at every sample point and every `g₀`: the self-pairing of the difference is
   `(A₁ − A₂) + (A₃ − A₄)` where `Aᵢ` are the four cross integrands.  Integrability of the four
   therefore gives integrability of the self-pairing, with no new hypothesis
   (`integrable_rootedPairing_diff_self`).  This is
   `Corrector/HarmonicGridIndependence.integrable_rootedSpecificPairingDensity_sub_self`
   transported to the sample-dependent vertex type of the coupled space.
2. **The reference field may be taken to be the first potential.**  `g₀` is universally
   quantified in the bridge, so it may be instantiated at `g₀ := firstPotential ms`.  Then the
   first and fourth cross pairings are pairings against the identically zero field, so `hi₁`,
   `hi₄`, `h₁` and `h₄` all hold outright (`rootedPairing_self_sub`).
3. **The two surviving relations are exchanged by the grid swap.**  The coupled law
   `ν ⊗ (gridLaw ⊗ gridLaw)` is invariant under `swapGrids : (e, D₁, D₂) ↦ (e, D₂, D₁)`
   (`measurePreserving_swapGrids`, from `Measure.measurePreserving_swap` — the two grid copies
   are i.i.d.), and `swapGrids` exchanges `firstPotential` with `secondPotential` *definitionally*
   (`firstPotential_swapGrids`).  Hence the third cross integrand is, after the swap, the negative
   of the second (`crossPairing_swapGrids`), and `hi₃`/`h₃` follow from `hi₂`/`h₂`.

## The three remaining inputs

`differenceFieldGridIndependent_of_cross_orthogonality`:

* `hi` — integrability of `p ↦ ⟪∇θ¹, ∇(θ² − θ¹)⟫(p)` on the coupled law;
* `horth` — the manuscript's cross orthogonality `∫ ⟪∇θ¹, ∇(θ² − θ¹)⟫ = 0`;
* `hmax` — `GridIndependenceDifferenceBridge.CopyDifferenceWeakMaximal ν ms`, unchanged.

Here `θ¹ = firstPotential ms` and `θ² = secondPotential ms` are the two grid-copy marked
potentials.

## Anti-vacuity: what `horth` actually is

`integral_rootedPairing_diff_self_eq` proves, from `hi` alone,

  `∫ ⟪∇(θ¹ − θ²), ∇(θ¹ − θ²)⟫ = −2 ∫ ⟪∇θ¹, ∇(θ² − θ¹)⟫`.

Since the left-hand side is pointwise nonnegative
(`HarmonicGridIndependence.rootedSpecificPairingDensity_self_nonneg`), `horth` is **exactly**
the vanishing of the expected specific energy of the difference at the origin — no more and no
less.  So the collapse `10 → 3` is an honest bookkeeping reduction and not a weakening: the
original ten inputs were jointly *stronger* than what the route consumes (they pinned four
cross pairings separately), and the three below are jointly *equivalent* to the origin step
`GridIndependenceCoupling.lintegral_origin_eq_zero_of_orthogonality` plus the maximal step.

Two consequences worth recording for whoever proves `horth`:

* `horth` cannot be obtained by any argument that does not, at bottom, prove
  `‖∇θ¹ − ∇θ²‖²_sp = 0`; conversely nothing weaker than `horth` suffices along this route.
  The manuscript's proof of it is the full variational orthogonality of each limiting potential
  over the *other* grid's blocks, which is **not** the local free-orthogonality identity
  `Corrector/LimitingPotentialFreeOrthogonality.dirichletForm_limit_eq_zero`: the latter is
  restricted to variations vanishing off a bounded rectangle, and `θ² − θ¹` does not vanish off
  a bounded set.
* `hi` is the only remaining *integrability* condition of the whole bridge.  By the termwise
  bound `2|⟪a,b⟫| ≤ ‖a‖² + ‖b‖²` of
  `Corrector/SpecificEnergyPolarization.integrable_rootedPairingDensity` it follows from
  finiteness of the two expected origin specific energies `E ρ_{θ¹}(0)`, `E ρ_{θ²}(0)` together
  with the corresponding measurability; the grid swap makes those two quantities equal, so it is
  really one finiteness statement.  That reduction is not carried out here because the
  measurability half is `hmeas`, owned elsewhere.

**This file proves no main theorem.**  The three remaining inputs are open; every statement
below is an implication.  The weld to the six-input assembly is machine-checked by the
partial-application `example` at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.CopyDifferenceInputReduction

open Code DyadicApproximation RootDensities HarmonicMainStatement EnvironmentLaws
open HarmonicLawIngredients
open MarkedLimitingCoordinateMeasurability HarmonicCoordinateAssembly GridIndependenceCoupling
open GridIndependenceDifferenceBridge

/-! ### Bilinearity of the rooted pairing in its second slot -/

/-- The rooted pairing of the coupled space is additive in the second slot.  This is
`Corrector/HarmonicGridIndependence.pairingSum_sub_right` read at each sample point with that
point's own vertex type; no algebra is reproved. -/
theorem rootedPairing_sub_right (Φ A B : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (p : CoupledSpace) :
    rootedPairing Φ (fun q u => A q u - B q u) p
      = rootedPairing Φ A p - rootedPairing Φ B p := by
  show HarmonicGridIndependence.rootedSpecificPairingDensity (decode p.1) (Φ p)
      (fun u => A p u - B p u) 0
      = HarmonicGridIndependence.rootedSpecificPairingDensity (decode p.1) (Φ p) (A p) 0
        - HarmonicGridIndependence.rootedSpecificPairingDensity (decode p.1) (Φ p) (B p) 0
  cases hroot : rootAt (decode p.1) (0 : Plane) with
  | none =>
      rw [HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_none _ _ _ hroot,
        HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_none _ _ _ hroot,
        HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_none _ _ _ hroot,
        sub_zero]
  | some v =>
      rw [HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_some _ _ _ hroot,
        HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_some _ _ _ hroot,
        HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_some _ _ _ hroot]
      show HarmonicGridIndependence.pairingSum (decode p.1) (Φ p) (fun u => A p u - B p u) v
            / (2 * StatementIngredients.cellArea (decode p.1) v)
          = HarmonicGridIndependence.pairingSum (decode p.1) (Φ p) (A p) v
              / (2 * StatementIngredients.cellArea (decode p.1) v)
            - HarmonicGridIndependence.pairingSum (decode p.1) (Φ p) (B p) v
              / (2 * StatementIngredients.cellArea (decode p.1) v)
      rw [HarmonicGridIndependence.pairingSum_sub_right (decode p.1) (decode_geometry p.1)
        (Φ p) (A p) (B p) v, sub_div]

/-- **Pairing against the zero field vanishes.**  This is what makes the choice
`g₀ := firstPotential ms` discharge two of the four cross relations outright. -/
theorem rootedPairing_self_sub (Φ A : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (p : CoupledSpace) :
    rootedPairing Φ (fun q u => A q u - A q u) p = 0 := by
  rw [rootedPairing_sub_right Φ A A p, sub_self]

/-- Antisymmetry of the rooted pairing under reversing the difference in its second slot. -/
theorem rootedPairing_neg_sub (Φ A B : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (p : CoupledSpace) :
    rootedPairing Φ (fun q u => A q u - B q u) p
      = - rootedPairing Φ (fun q u => B q u - A q u) p := by
  rw [rootedPairing_sub_right Φ A B p, rootedPairing_sub_right Φ B A p, neg_sub]

/-! ### `hint` is free -/

/-- **The self-pairing of the difference is integrable as soon as the four cross pairings are.**
The polarization identity `GridIndependenceCoupling.rootedPairing_sub_self` holds at *every*
sample point, so this costs no hypothesis beyond `hi₁ … hi₄`; in particular the bridge's tenth
input `hint` is not an independent assumption. -/
theorem integrable_rootedPairing_diff_self (μ : Measure CoupledSpace)
    (g₀ g₁ g₂ : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (hi₁ : Integrable (rootedPairing g₁ fun q u => g₁ q u - g₀ q u) μ)
    (hi₂ : Integrable (rootedPairing g₁ fun q u => g₂ q u - g₀ q u) μ)
    (hi₃ : Integrable (rootedPairing g₂ fun q u => g₂ q u - g₀ q u) μ)
    (hi₄ : Integrable (rootedPairing g₂ fun q u => g₁ q u - g₀ q u) μ) :
    Integrable (rootedPairing (fun q u => g₁ q u - g₂ q u)
      fun q u => g₁ q u - g₂ q u) μ :=
  ((hi₁.sub hi₂).add (hi₃.sub hi₄)).congr
    (Filter.Eventually.of_forall fun p => (rootedPairing_sub_self g₀ g₁ g₂ p).symm)

/-! ### `hcopies` from two cross relations -/

/-! ### The grid swap -/

/-- Exchange of the two independent grid copies on the coupled space. -/
def swapGrids (p : CoupledSpace) : CoupledSpace := (p.1, p.2.2, p.2.1)

theorem swapGrids_eq :
    swapGrids
      = Prod.map (id : Env → Env) (Prod.swap : Grid × Grid → Grid × Grid) := by
  funext p
  obtain ⟨e, D₁, D₂⟩ := p
  rfl

theorem measurableEmbedding_swapGrids : MeasurableEmbedding swapGrids := by
  have hfun : swapGrids
      = ⇑((MeasurableEquiv.refl Env).prodCongr (MeasurableEquiv.prodComm)) := by
    funext p
    obtain ⟨e, D₁, D₂⟩ := p
    rfl
  rw [hfun]
  exact MeasurableEquiv.measurableEmbedding _

/-- **The coupled law is invariant under exchanging the two grid copies.**  The two grids are
independent with the same law, so this is `Measure.measurePreserving_swap` on the second
factor; no property of `gridLaw` beyond `ν ⊗ (gridLaw ⊗ gridLaw)` being a product is used. -/
theorem measurePreserving_swapGrids (ν : Measure Env) [SFinite ν] :
    MeasurePreserving swapGrids (ν.prod (gridLaw.prod gridLaw))
      (ν.prod (gridLaw.prod gridLaw)) := by
  rw [swapGrids_eq]
  exact (MeasurePreserving.id ν).prod Measure.measurePreserving_swap

/-- **The third cross integrand is the negative of the second, composed with the swap.** -/
theorem crossPairing_swapGrids (ms : ℕ → ℕ) (p : CoupledSpace) :
    rootedPairing (secondPotential ms)
        (fun q u => secondPotential ms q u - firstPotential ms q u) (swapGrids p)
      = - rootedPairing (firstPotential ms)
          (fun q u => secondPotential ms q u - firstPotential ms q u) p := by
  have h : rootedPairing (secondPotential ms)
        (fun q u => secondPotential ms q u - firstPotential ms q u) (swapGrids p)
      = rootedPairing (firstPotential ms)
          (fun q u => firstPotential ms q u - secondPotential ms q u) p := rfl
  rw [h, rootedPairing_neg_sub]

/-- `hi₃` from `hi₂`. -/
theorem integrable_secondCross_of_first (ν : Measure Env) [SFinite ν] (ms : ℕ → ℕ)
    (hi : Integrable (rootedPairing (firstPotential ms)
      fun q u => secondPotential ms q u - firstPotential ms q u)
      (ν.prod (gridLaw.prod gridLaw))) :
    Integrable (rootedPairing (secondPotential ms)
      fun q u => secondPotential ms q u - firstPotential ms q u)
      (ν.prod (gridLaw.prod gridLaw)) := by
  have hcomp : Integrable
      ((rootedPairing (secondPotential ms)
        fun q u => secondPotential ms q u - firstPotential ms q u) ∘ swapGrids)
      (ν.prod (gridLaw.prod gridLaw)) := by
    have hfun : ((rootedPairing (secondPotential ms)
        fun q u => secondPotential ms q u - firstPotential ms q u) ∘ swapGrids)
        = fun p : CoupledSpace => -(rootedPairing (firstPotential ms)
          (fun q u => secondPotential ms q u - firstPotential ms q u) p) :=
      funext fun p => crossPairing_swapGrids ms p
    rw [hfun]
    exact hi.neg
  exact ((measurePreserving_swapGrids ν).integrable_comp_emb measurableEmbedding_swapGrids).1
    hcomp

/-- **The two cross expectations are opposite**, by the grid swap. -/
theorem integral_secondCross_eq_neg (ν : Measure Env) [SFinite ν] (ms : ℕ → ℕ) :
    (∫ p, rootedPairing (secondPotential ms)
      (fun q u => secondPotential ms q u - firstPotential ms q u) p
        ∂ν.prod (gridLaw.prod gridLaw))
      = -∫ p, rootedPairing (firstPotential ms)
          (fun q u => secondPotential ms q u - firstPotential ms q u) p
            ∂ν.prod (gridLaw.prod gridLaw) := by
  have key := (measurePreserving_swapGrids ν).integral_comp measurableEmbedding_swapGrids
    (rootedPairing (secondPotential ms)
      fun q u => secondPotential ms q u - firstPotential ms q u)
  rw [← key]
  simp only [crossPairing_swapGrids]
  rw [integral_neg]

/-! ### The three-input reduction -/

/-! ### Anti-vacuity: `horth` *is* the vanishing of the expected specific energy -/

/-- **The content of `horth`, made explicit.**  On the coupled law the expected specific energy
of the difference of the two grid-copy potentials is exactly `−2` times the cross pairing that
`horth` sets to zero.  Since the left-hand side is pointwise nonnegative, `horth` is equivalent
to its vanishing: the three-input reduction is neither vacuous nor a weakening. -/
theorem integral_rootedPairing_diff_self_eq (ν : Measure Env) [SFinite ν] (ms : ℕ → ℕ)
    (hi : Integrable (rootedPairing (firstPotential ms)
      fun q u => secondPotential ms q u - firstPotential ms q u)
      (ν.prod (gridLaw.prod gridLaw))) :
    (∫ p, rootedPairing (fun q u => firstPotential ms q u - secondPotential ms q u)
      (fun q u => firstPotential ms q u - secondPotential ms q u) p
        ∂ν.prod (gridLaw.prod gridLaw))
      = -2 * ∫ p, rootedPairing (firstPotential ms)
          (fun q u => secondPotential ms q u - firstPotential ms q u) p
            ∂ν.prod (gridLaw.prod gridLaw) := by
  have hi₃ := integrable_secondCross_of_first ν ms hi
  have hpt : ∀ p : CoupledSpace,
      rootedPairing (fun q u => firstPotential ms q u - secondPotential ms q u)
        (fun q u => firstPotential ms q u - secondPotential ms q u) p
        = rootedPairing (secondPotential ms)
            (fun q u => secondPotential ms q u - firstPotential ms q u) p
          - rootedPairing (firstPotential ms)
            (fun q u => secondPotential ms q u - firstPotential ms q u) p := by
    intro p
    rw [rootedPairing_sub_self (firstPotential ms) (firstPotential ms) (secondPotential ms) p]
    simp only [rootedPairing_self_sub]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hi₃ hi,
    integral_secondCross_eq_neg ν ms]
  ring

/-! ### The weld to the six-input assembly, machine-checked

The producer fills the `hcopies` slot of
`Corrector/HarmonicCoordinateSixInputs.harmonicCoordinateConclusions_of_six_inputs` with no
coercion and no hypothesis that the consumer does not already bind, beyond the three inputs of
this module; what is left over is exactly `hsub` and `hspec`. -/

end ReflectedGMS.CopyDifferenceInputReduction
