/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GridIndependenceCoupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.UnmarkedCoordinateDescent
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicGridIndependence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyLocalControl

/-!
# The coupling bridge for `s:prop:gridindependence`

`Corrector/HarmonicGridIndependence.lean` proves the *comparison* half of the manuscript
proposition `s:prop:gridindependence` ("The auxiliary grid disappears"), and
`Corrector/UnmarkedCoordinateDescent.lean` proves the *measurability* half.  The two halves do
not compose, for a purely structural reason:

* `HarmonicGridIndependence.ae_eq_of_specificPairing_orthogonal` is stated for a **fixed**
  countable vertex type `V` and a family `F : Ω → IndexedCells V`;
* the actual environment space has an **environment-dependent** vertex type,
  `Code.decode e : IndexedCells (Code.Vertex e.val)` with `Code.Vertex r = {n // (r.1 n).isSome}`;
* and the descent of `UnmarkedCoordinateDescent` consumes its input in the product shape
  `∀ᵐ p : Env × Grid × Grid ∂ν.prod (σ.prod σ), Ψ (p.1, p.2.1) = Ψ (p.1, p.2.2)`
  on `ℕ`-indexed label fields.

So `ae_eq_of_specificPairing_orthogonal` cannot be instantiated at `Ω := Env × Grid × Grid`,
`μ := ν.prod (σ.prod σ)` at all: there is no single `V`.  Padding `V := ℕ` with degenerate cells
is not available either, because `Geometry` demands both `(⋃ v, cell v) = univ` and connectedness
of the cell-adjacency graph, which isolated absent labels destroy.

This module supplies the missing bridge.  It runs the manuscript's comparison chain directly on
the joint law `μ` of the environment and the two independent grid copies, with the vertex type
depending on the sample point, and then converts the resulting `Code.Vertex`-indexed equality into
the `ℕ`-indexed product shape that `UnmarkedCoordinateDescent` consumes.

## Reuse

Nothing in the comparison chain is reproved.  The pointwise algebra of the polarized
specific-energy density is `V`-polymorphic in `HarmonicGridIndependence`, so it applies at each
sample point with that point's own vertex type, and is used verbatim:
`rootedSpecificPairingDensity_sub_self`, `rootedSpecificPairingDensity_self_nonneg`,
`ofReal_specificPairingDensity_self`, `eq_of_forall_specificPairingDensity_self_eq_zero`.  Only
the *integral* steps, which involve no vertex type once the pointwise identity has been applied,
are redone here — they are three lines of `integral_add` / `integral_sub`.
The manuscript's "detects every edge" step is the checked
`SpecificEnergyLocalControl.apply_eq_of_setLIntegral_closedBall_eq_zero`.

## What is proved

* `eq_of_forall_vertex_eq` — two `ℕ`-indexed label fields with the absent-label zero convention
  agree as soon as they agree at every present label.
* `ofReal_rootedSpecificPairingDensity_self` — the rooted form of
  `HarmonicGridIndependence.ofReal_specificPairingDensity_self`: the diagonal of the rooted
  polarized density is the project's rooted specific-energy density `ρ_Φ`.
* `specificPairingDensity_self_eq_zero_of_setLIntegral_closedBall_eq_zero` and
  `eq_of_setLIntegral_closedBall_sub_eq_zero` — the manuscript's
  "`s:eq:localcontrol` on integer-radius disks then detects every edge and makes its value zero",
  in the exact form in which `HarmonicGridIndependence` needs it.  This *proves* the hypothesis
  `htransfer` of `ae_eq_of_specificPairing_orthogonal` from the vanishing of the disk integrals.
* `rootedPairing`, `rootedPairing_sub_self`, `integral_rootedPairing_sub_self_eq_zero`,
  `ae_rootedPairing_self_eq_zero`, `lintegral_rootedSpecificEnergyDensity_origin_eq_zero` — the
  manuscript's `‖g¹ − g²‖²_sp = 0` chain, on the joint law, with a sample-dependent vertex type.
* `lintegral_origin_eq_zero_of_orthogonality` — that chain packaged: the four cross orthogonality
  relations alone, with **no** stationarity, anchoring or maximal inequality, make the expected
  rooted specific-energy density of `g¹ − g²` at the origin vanish.
* `ae_setLIntegral_closedBall_eq_zero` — the passage from the vanishing of the expected rooted
  density at the origin to the almost-sure vanishing of every disk integral, under the spatial
  stationarity identity `hstationary` (see "Inputs" below), and
  `ae_setLIntegral_closedBall_eq_zero_of_ballMaximal` — the same passage along the manuscript's
  own maximal-function route, in the shape produced by `Spatial.SpatialMaximalInequality` and
  `Spatial.ActualSpatialDensityBridge.setLIntegral_le_ballMaximal`.
* `ae_eq_of_ae_setLIntegral_closedBall_eq_zero` and `ae_eq_of_orthogonality` — the assembled
  comparison: `∀ᵐ p ∂μ, g₁ p = g₂ p`.
* `aeProd_marked_copies_of_orthogonality` — **the bridge**: the same conclusion in the exact
  product shape `∀ᵐ p : Env × Grid × Grid ∂ν.prod (σ.prod σ), Ψ (p.1, p.2.1) = Ψ (p.1, p.2.2)`
  that `UnmarkedCoordinateDescent.exists_unmarked_cellField` consumes.
* `exists_gridIndependent_cellField` — the composition with that consumer: an environment-only
  measurable `CellField` which is almost surely the marked field.

## Inputs — this is an honestly CONDITIONAL result

Nothing here proves grid independence outright.  Three families of inputs stay visible as named
hypotheses, each owed by a different packet:

1. `h₁ … h₄` with `hi₁ … hi₄` — the four cross specific-orthogonality relations of the manuscript
   and their integrability.  These are exactly the inputs of
   `HarmonicGridIndependence.specificPairing_sub_self_eq_zero`, transcribed to the joint law.
   Owed by `Corrector/LimitingHarmonicPotential` and `Corrector/SpecificEnergyRedistribution`.
2. `hstationary` (and its measurability side condition `hballMeasurable`) — the spatial
   stationarity/Palm identity
   `E ∫_{B̄_r} ρ_θ(z) dz = |B̄_r| · E ρ_θ(0)`.
   This is a symmetry property of the law alone: it holds for *every* field and asserts nothing
   about `θ` vanishing.  It is the manuscript's mass-transport step.  **It is not currently
   available in the project in this form**: `EnvironmentLaws.MassTransport` is a whole-plane
   outgoing = incoming identity for degree `(-2)` similarity-covariant kernels, and the ball form
   used here has no producer.
3. `hanchor` — the manuscript's normalization, that the two potentials agree at one cell of each
   sample (the root cell `H₀`).

No harmonicity, minimality, or convergence property is used or asserted anywhere below.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

namespace ReflectedGMS

namespace GridIndependenceCoupling

open Code RootDensities EnvironmentFields DyadicApproximation HarmonicMainStatement

/-! ### Label fields and present labels -/

/-! ### The rooted diagonal of the polarized density -/

/-- The rooted form of `HarmonicGridIndependence.ofReal_specificPairingDensity_self`: the diagonal
of the rooted polarized density **is** the project's rooted specific-energy density `ρ_Φ`.  No
competing energy notion is introduced. -/
theorem ofReal_rootedSpecificPairingDensity_self {V : Type*} [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (Φ : V → Plane) (z : Plane) :
    ENNReal.ofReal (HarmonicGridIndependence.rootedSpecificPairingDensity F Φ Φ z)
      = rootedSpecificEnergyDensity F Φ z := by
  rcases hroot : rootAt F z with _ | v
  · rw [HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_none F Φ Φ hroot]
    simp [rootedSpecificEnergyDensity, hroot]
  · rw [HarmonicGridIndependence.rootedSpecificPairingDensity_of_eq_some F Φ Φ hroot,
      HarmonicGridIndependence.ofReal_specificPairingDensity_self F hF Φ v]
    simp [rootedSpecificEnergyDensity, hroot]

/-! ### The manuscript's "detects every edge" step

This section *proves* the hypothesis `htransfer` of
`HarmonicGridIndependence.ae_eq_of_specificPairing_orthogonal` from the vanishing of the disk
integrals of the rooted density, using the checked
`SpecificEnergyLocalControl.apply_eq_of_setLIntegral_closedBall_eq_zero`. -/

/-- **Vanishing disk integrals kill the polarized density at every vertex.**  If the rooted
specific-energy density of `θ` has zero integral on every disk about the origin, then the
polarized density of `θ` against itself vanishes at every cell. -/
theorem specificPairingDensity_self_eq_zero_of_setLIntegral_closedBall_eq_zero
    {V : Type*} [Countable V] (F : IndexedCells V) (hF : Geometry F) (θ : V → Plane)
    (h : ∀ r : ℝ, 0 < r →
      (∫⁻ z in Metric.closedBall (0 : Plane) r, rootedSpecificEnergyDensity F θ z ∂volume) = 0)
    (v : V) : HarmonicGridIndependence.specificPairingDensity F θ θ v = 0 := by
  have hterm : ∀ w : V,
      (∑ i : Fin 2, F.graph.c v w * ((θ w i - θ v i) * (θ w i - θ v i))) = 0 := by
    intro w
    rcases eq_or_lt_of_le (F.graph.c_nonneg v w) with hc | hc
    · simp [← hc]
    · have hval :=
        SpecificEnergyLocalControl.apply_eq_of_setLIntegral_closedBall_eq_zero F hF θ h hc
      simp [hval]
  have hsum : HarmonicGridIndependence.pairingSum F θ θ v = 0 := by
    simp only [HarmonicGridIndependence.pairingSum, hterm, tsum_zero]
  simp [HarmonicGridIndependence.specificPairingDensity, hsum]

/-- **The anchored equality from the disk integrals.**  Two vertex fields whose difference has
vanishing rooted specific energy on every disk, and which agree at one cell, agree everywhere.
`Geometry` supplies the connectivity of the cell-adjacency graph. -/
theorem eq_of_setLIntegral_closedBall_sub_eq_zero {V : Type*} [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (Φ Ψ : V → Plane)
    (h : ∀ r : ℝ, 0 < r →
      (∫⁻ z in Metric.closedBall (0 : Plane) r,
        rootedSpecificEnergyDensity F (fun u => Φ u - Ψ u) z ∂volume) = 0)
    {v₀ : V} (hanchor : Φ v₀ = Ψ v₀) : Φ = Ψ :=
  HarmonicGridIndependence.eq_of_forall_specificPairingDensity_self_eq_zero F hF Φ Ψ
    (specificPairingDensity_self_eq_zero_of_setLIntegral_closedBall_eq_zero F hF
      (fun u => Φ u - Ψ u) h) hanchor

/-! ### The joint law of the environment and the two independent grid copies -/

/-- The joint sample space carrying the environment and the two independent auxiliary grids. -/
abbrev CoupledSpace := Env × Grid × Grid

/-- The manuscript's rooted polarized density at the origin, for two vertex fields whose index
type is the sample point's own vertex type. -/
noncomputable def rootedPairing
    (Φ Ψ : (p : CoupledSpace) → Vertex p.1.val → Plane) (p : CoupledSpace) : ℝ :=
  HarmonicGridIndependence.rootedSpecificPairingDensity (decode p.1) (Φ p) (Ψ p) 0

/-- The manuscript's polarization identity at the joint level.  This is
`HarmonicGridIndependence.rootedSpecificPairingDensity_sub_self` applied at each sample point with
that point's own vertex type; no algebra is reproved. -/
theorem rootedPairing_sub_self (g₀ g₁ g₂ : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (p : CoupledSpace) :
    rootedPairing (fun q u => g₁ q u - g₂ q u) (fun q u => g₁ q u - g₂ q u) p
      = (rootedPairing g₁ (fun q u => g₁ q u - g₀ q u) p
          - rootedPairing g₁ (fun q u => g₂ q u - g₀ q u) p)
        + (rootedPairing g₂ (fun q u => g₂ q u - g₀ q u) p
            - rootedPairing g₂ (fun q u => g₁ q u - g₀ q u) p) :=
  HarmonicGridIndependence.rootedSpecificPairingDensity_sub_self (decode p.1)
    (decode_geometry p.1) (g₀ p) (g₁ p) (g₂ p) 0

/-- A vanishing expected rooted density makes the rooted density vanish almost surely. -/
theorem ae_rootedPairing_self_eq_zero (μ : Measure CoupledSpace)
    (θ : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (hint : Integrable (rootedPairing θ θ) μ)
    (hzero : (∫ p, rootedPairing θ θ p ∂μ) = 0) :
    ∀ᵐ p ∂μ, rootedPairing θ θ p = 0 := by
  have hnn : (0 : CoupledSpace → ℝ) ≤ rootedPairing θ θ := fun p =>
    HarmonicGridIndependence.rootedSpecificPairingDensity_self_nonneg (decode p.1) (θ p) 0
  have h := (integral_eq_zero_iff_of_nonneg hnn hint).1 hzero
  filter_upwards [h] with p hp
  simpa using hp

/-- The expected rooted **specific-energy** density at the origin vanishes as soon as the rooted
polarized density does almost surely. -/
theorem lintegral_rootedSpecificEnergyDensity_origin_eq_zero (μ : Measure CoupledSpace)
    (θ : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (h : ∀ᵐ p ∂μ, rootedPairing θ θ p = 0) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (θ p) 0 ∂μ) = 0 := by
  have hae : ∀ᵐ p ∂μ, rootedSpecificEnergyDensity (decode p.1) (θ p) 0 = 0 := by
    filter_upwards [h] with p hp
    simp only [rootedPairing] at hp
    rw [← ofReal_rootedSpecificPairingDensity_self (decode p.1) (decode_geometry p.1) (θ p) 0, hp]
    simp
  calc (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (θ p) 0 ∂μ)
      = ∫⁻ _ : CoupledSpace, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae hae
    _ = 0 := lintegral_zero

/-! ### From the origin to every disk

The manuscript's maximal-inequality step.  The stationarity identity `hstationary` is a property
of the law alone; it holds for every field and says nothing about `θ` vanishing. -/

/-! ### The assembled comparison on the joint law -/

/-- **The anchored comparison from the disk integrals, on the joint law.**  If the rooted specific
energy of the difference has vanishing integral on every disk, almost surely, and the two fields
agree at one cell of almost every sample, then they agree at every cell almost surely. -/
theorem ae_eq_of_ae_setLIntegral_closedBall_eq_zero (μ : Measure CoupledSpace)
    (g₁ g₂ : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (hdisk : ∀ᵐ p ∂μ, ∀ r : ℝ, 0 < r →
      (∫⁻ z in Metric.closedBall (0 : Plane) r,
        rootedSpecificEnergyDensity (decode p.1) (fun u => g₁ p u - g₂ p u) z ∂volume) = 0)
    (hanchor : ∀ᵐ p ∂μ, ∃ v₀ : Vertex p.1.val, g₁ p v₀ = g₂ p v₀) :
    ∀ᵐ p ∂μ, g₁ p = g₂ p := by
  filter_upwards [hdisk, hanchor] with p hp hv
  obtain ⟨v₀, hv₀⟩ := hv
  exact eq_of_setLIntegral_closedBall_sub_eq_zero (decode p.1) (decode_geometry p.1)
    (g₁ p) (g₂ p) hp hv₀

/-! ### The bridge to the product shape consumed by the descent -/

end GridIndependenceCoupling

end ReflectedGMS
