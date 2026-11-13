/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.CopyDifferenceOrthogonalityLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CopyDifferenceCrossPairing
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CopyDifferenceOriginEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.HarmonicCoordinateThreeInputs
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolantSelectionCandidate

/-!
# `hzero`: the cross orthogonality of the two grid copies, and the harmonic theorem's count

This is the second half of the manuscript's proof of `s:prop:gridindependence` (tex:583):

> *Send `m → ∞` to obtain `⟪g¹, g² − g₀⟫ = 0`.  Also `⟪g¹, g¹ − g₀⟫ = 0` by the same argument
> with the first grid.  Hence `⟪g¹, g¹ − g²⟫ = 0`.*

`Corrector/CopyDifferenceCrossPairing` gives, at every positive stage `m`, the two identities
`⟪Φ², V_m⟫_* = 0` and `⟪Φ¹, V_m⟫_* = 0` on the coupled law `ν ⊗ (𝔻 ⊗ 𝔻)`, with `V_m` the gated
variation `φ_m¹ − b` of the block grid and `Φⁱ` the limiting potential of grid `i`.  The grid
swap (`CopyDifferenceInputReduction.swapGrids`, measure preserving) turns the first into
`⟪Φ¹, V_m ∘ swap⟫_* = 0`, whose variation is `φ_m² − b`.  Subtracting, the centroid field `b`
cancels **before** any limit is taken:

  `⟪Φ¹, (φ_m² − b) − (φ_m¹ − b)⟫ = ⟪Φ¹, φ_m² − Φ²⟫ − (⟪Φ¹, φ_m¹ − Φ¹⟫ − ⟪Φ¹, Φ² − Φ¹⟫)`,

so the expected cross pairing `E⟪Φ¹, Φ² − Φ¹⟫` equals `E⟪Φ¹, φ_m¹ − Φ¹⟫ − E⟪Φ¹, φ_m² − Φ²⟫` at
every stage, and both terms tend to zero by
`GridCrossOrthogonalityPolarization.tendsto_integral_rootedPairingDensity_of_tendsto_zero`
because `E ρ_{φ_m − Φ} → 0` (`hspec`, itself produced from `hproj`).  Hence the cross pairing
vanishes, which is `horth` of `Corrector/CopyDifferenceOriginEnergy`, and `hzero` follows.

## What is DISCHARGED and what is REDUCED

* **`hzero` is DISCHARGED** (`originEnergy_eq_zero`) from the manuscript's own `s:eq:MTP` and
  (FE) moment, the assembly's `hmeas`, the nested projection bound `hproj`, and the two
  convergence inputs `hconv`, `hpatch` — all of which the three-input head already manufactures
  from `hproj` and `hmeas` along the subsequence `hproj` produces.
* **The harmonic-coordinate theorem is REDUCED to `hproj` alone**
  (`harmonicCoordinateConclusions_of_projection`): `hmeas` is discharged by
  `Corrector/BlockInterpolantSelectionCandidate.measurable_gatedApproximant`, and `hzero` by this
  module.  `harmonicCoordinateConclusions_of_two_inputs` keeps `hmeas` as a binder for callers
  that do not want that dependency.

**This file proves no main theorem**: `hproj` (`SpecificEnergyConvergence.MarkedNestedProjectionBound`)
remains a named open input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.CopyDifferenceOrthogonalityLimit

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open DyadicGridLaw GridIndependenceCoupling GridIndependenceDifferenceBridge
open CopyDifferenceInputReduction SpecificEnergyPolarization
open GridCrossOrthogonalityPolarization GridCrossOrthogonalityOwnership
open CopyDifferenceCrossPairing MarkedDensityMeasurabilityProducer GoodMarkedSpace

/-! ### The grid swap on the coupled fields -/

section Limit

variable (ν : Measure Env) [IsProbabilityMeasure ν]

/-- **The swapped cross identity** `⟪Φ¹, φ_m² − b⟫_* = 0`: the cross identity read through the
measure-preserving grid swap. -/
theorem integral_swappedCrossPairing_eq_zero (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (m : ℕ) (hm : m ≠ 0) :
    (∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p)
        (gatedVariation m (swapGrids p)) 0 ∂(ν.prod (gridMeasure.prod gridMeasure))) = 0 := by
  have h := integral_crossPairing_eq_zero ν hν hFE ms hms hmeas hproj hconv hpatch m hm
  have key := (measurePreserving_swapGrids ν).integral_comp measurableEmbedding_swapGrids
    (fun q : CoupledSpace =>
      rootedPairingDensity (decode q.1) (crossPotential ms q) (gatedVariation m q) 0)
  have hEq : (fun p : CoupledSpace => rootedPairingDensity (decode p.1) (blockPotential ms p)
        (gatedVariation m (swapGrids p)) 0)
      = fun p : CoupledSpace => (fun q : CoupledSpace =>
          rootedPairingDensity (decode q.1) (crossPotential ms q) (gatedVariation m q) 0)
          (swapGrids p) := rfl
  rw [hEq, key]
  exact h

/-! ### Transport of `lintegral`s along the two projections, for `AEMeasurable` integrands -/

theorem lintegral_comp_passiveMarked (F : MarkedEnvironment → ℝ≥0∞)
    (hF : AEMeasurable F (ν.prod gridMeasure)) :
    (∫⁻ p, F (passiveMarked p) ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ ω, F ω ∂(ν.prod gridMeasure) := by
  have hmp := measurePreserving_passiveMarked ν
  have hF' : AEMeasurable F
      (Measure.map passiveMarked (ν.prod (gridMeasure.prod gridMeasure))) := by
    rw [hmp.map_eq]
    exact hF
  rw [← lintegral_map' hF' measurable_passiveMarked.aemeasurable, hmp.map_eq]

theorem lintegral_comp_blockMarked (F : MarkedEnvironment → ℝ≥0∞)
    (hF : AEMeasurable F (ν.prod gridMeasure)) :
    (∫⁻ p, F (blockMarked p) ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ ω, F ω ∂(ν.prod gridMeasure) := by
  have hmp := measurePreserving_blockMarked ν
  have hF' : AEMeasurable F
      (Measure.map blockMarked (ν.prod (gridMeasure.prod gridMeasure))) := by
    rw [hmp.map_eq]
    exact hF
  rw [← lintegral_map' hF' measurable_blockMarked.aemeasurable, hmp.map_eq]

/-! ### Label representations of the stage errors -/

/-- The label field of the stage error `φ_m² − Φ²` of the passive grid. -/
noncomputable def passiveErrorLabel (ms : ℕ → ℕ) (m : ℕ) (p : CoupledSpace) (n : ℕ) : Plane :=
  gatedApproximant m (p.1, p.2.2) n - crossLabel ms p n

/-- The label field of the stage error `φ_m¹ − Φ¹` of the block grid. -/
noncomputable def blockErrorLabel (ms : ℕ → ℕ) (m : ℕ) (p : CoupledSpace) (n : ℕ) : Plane :=
  gatedApproximant m (p.1, p.2.1) n - blockLabel ms p n

theorem measurable_passiveErrorLabel (ms : ℕ → ℕ) (m : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) (n : ℕ) :
    Measurable fun p : CoupledSpace => passiveErrorLabel ms m p n := by
  have h1 : Measurable fun p : CoupledSpace => gatedApproximant m (p.1, p.2.2) n :=
    (hmeas m n).comp measurable_passiveMarked
  exact h1.sub (measurable_crossLabel ms hmeas n)

theorem measurable_blockErrorLabel (ms : ℕ → ℕ) (m : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) (n : ℕ) :
    Measurable fun p : CoupledSpace => blockErrorLabel ms m p n := by
  have h1 : Measurable fun p : CoupledSpace => gatedApproximant m (p.1, p.2.1) n :=
    (hmeas m n).comp measurable_blockMarked
  exact h1.sub (measurable_blockLabel ms hmeas n)

/-- On the sublinear event the passive stage error is its label field. -/
theorem passiveError_eq_label (ms : ℕ → ℕ) (m : ℕ) {p : CoupledSpace}
    (hG : p.1 ∈ SublinearEvent) :
    (fun v : Vertex p.1.val => phi (decode p.1) p.2.2 m v - crossPotential ms p v)
      = fun v : Vertex p.1.val => passiveErrorLabel ms m p v.val := by
  funext v
  show phi (decode p.1) p.2.2 m v - crossPotential ms p v
    = gatedApproximant m (p.1, p.2.2) v.val - crossLabel ms p v.val
  rw [phi_eq_gatedApproximant (m := m) (ω := (p.1, p.2.2)) hG v]
  rfl

theorem blockError_eq_label (ms : ℕ → ℕ) (m : ℕ) {p : CoupledSpace}
    (hG : p.1 ∈ SublinearEvent) :
    (fun v : Vertex p.1.val => phi (decode p.1) p.2.1 m v - blockPotential ms p v)
      = fun v : Vertex p.1.val => blockErrorLabel ms m p v.val := by
  funext v
  show phi (decode p.1) p.2.1 m v - blockPotential ms p v
    = gatedApproximant m (p.1, p.2.1) v.val - blockLabel ms p v.val
  rw [phi_eq_gatedApproximant (m := m) (ω := (p.1, p.2.1)) hG v]
  rfl

/-! ### The pointwise decomposition -/

/-- **The centroid field cancels before the limit.**  Wherever both gated variations are the
concrete `φ_m − b`,
`⟪Φ¹, V_m∘swap⟫ − ⟪Φ¹, V_m⟫ = ⟪Φ¹, φ_m² − Φ²⟫ − (⟪Φ¹, φ_m¹ − Φ¹⟫ − ⟪Φ¹, Φ² − Φ¹⟫)`. -/
theorem pairing_decomposition (ms : ℕ → ℕ) (m : ℕ) (p : CoupledSpace)
    (hW : gatedVariation m (swapGrids p)
      = fun v => phi (decode p.1) p.2.2 m v - cellCentroid (decode p.1) v)
    (hV : gatedVariation m p
      = fun v => phi (decode p.1) p.2.1 m v - cellCentroid (decode p.1) v) :
    rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m (swapGrids p)) 0
        - rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m p) 0
      = rootedPairingDensity (decode p.1) (blockPotential ms p)
          (fun v => phi (decode p.1) p.2.2 m v - crossPotential ms p v) 0
        - (rootedPairingDensity (decode p.1) (blockPotential ms p)
            (fun v => phi (decode p.1) p.2.1 m v - blockPotential ms p v) 0
          - rootedPairingDensity (decode p.1) (blockPotential ms p)
            (fun v => crossPotential ms p v - blockPotential ms p v) 0) := by
  have hF : Geometry (decode p.1) := decode_geometry p.1
  have h1 := rootedPairingDensity_sub_right (decode p.1) hF (blockPotential ms p)
    (gatedVariation m (swapGrids p)) (gatedVariation m p) 0
  have h3 := rootedPairingDensity_sub_right (decode p.1) hF (blockPotential ms p)
    (fun v => phi (decode p.1) p.2.1 m v - blockPotential ms p v)
    (fun v => crossPotential ms p v - blockPotential ms p v) 0
  have h2 := rootedPairingDensity_sub_right (decode p.1) hF (blockPotential ms p)
    (fun v => phi (decode p.1) p.2.2 m v - crossPotential ms p v)
    (fun u => (fun v => phi (decode p.1) p.2.1 m v - blockPotential ms p v) u
      - (fun v => crossPotential ms p v - blockPotential ms p v) u) 0
  rw [← h1, ← h3, ← h2]
  congr 1
  funext v
  simp only [hW, hV]
  abel

/-! ### The energies of the fields entering the decomposition -/

theorem measurable_rootedSpecificEnergyDensity_blockPotential (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable fun p : CoupledSpace =>
      rootedSpecificEnergyDensity (decode p.1) (blockPotential ms p) 0 :=
  (measurable_rootedSpecificEnergyDensity_markedPotential ms hmeas).comp measurable_blockMarked

theorem measurable_rootedSpecificEnergyDensity_crossPotential (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable fun p : CoupledSpace =>
      rootedSpecificEnergyDensity (decode p.1) (crossPotential ms p) 0 :=
  (measurable_rootedSpecificEnergyDensity_markedPotential ms hmeas).comp measurable_passiveMarked

theorem lintegral_rootedSpecificEnergyDensity_blockPotential_ne_top (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (blockPotential ms p) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞ := by
  have hspec := SpecificEnergyConvergence.markedSpecificEnergyConvergence_of_nestedProjection ν hν
    hFE hmeas hproj ms hms hconv
  have hdens := markedDensityMeasurability_of_massTransport ν hν hFE.ne ms hmeas
  rw [lintegral_rootedSpecificEnergyDensity_blockPotential ν ms hmeas]
  exact (lintegral_rootedSpecificEnergyDensity_markedPotential_lt_top ν ms hdens hspec).ne

theorem lintegral_rootedSpecificEnergyDensity_crossPotential_ne_top (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (crossPotential ms p) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞ := by
  have hspec := SpecificEnergyConvergence.markedSpecificEnergyConvergence_of_nestedProjection ν hν
    hFE hmeas hproj ms hms hconv
  have hdens := markedDensityMeasurability_of_massTransport ν hν hFE.ne ms hmeas
  rw [lintegral_rootedSpecificEnergyDensity_crossPotential ν ms hmeas]
  exact (lintegral_rootedSpecificEnergyDensity_markedPotential_lt_top ν ms hdens hspec).ne

/-- The gated variation as a label field, on the whole coupled space. -/
theorem gatedVariation_eq_label_field (m : ℕ) (p : CoupledSpace) :
    gatedVariation m p = fun v : Vertex p.1.val => variationLabel m p v.val :=
  funext fun v => gatedVariation_eq_label m p v

theorem measurable_rootedSpecificEnergyDensity_gatedVariation (m : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable fun p : CoupledSpace =>
      rootedSpecificEnergyDensity (decode p.1) (gatedVariation m p) 0 := by
  have h := MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (Prod.fst : CoupledSpace → Env)) measurable_fst (Ψ := variationLabel m)
    (measurable_variationLabel m hmeas)
  have hEq : (fun p : CoupledSpace => rootedSpecificEnergyDensity (decode p.1)
        (fun v : Vertex p.1.val => variationLabel m p v.val) 0)
      = fun p : CoupledSpace => rootedSpecificEnergyDensity (decode p.1) (gatedVariation m p) 0 := by
    funext p
    rw [gatedVariation_eq_label_field m p]
  rw [hEq] at h
  exact h

theorem measurable_rootedSpecificEnergyDensity_swappedVariation (m : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable fun p : CoupledSpace =>
      rootedSpecificEnergyDensity (decode p.1) (gatedVariation m (swapGrids p)) 0 := by
  have h := (measurable_rootedSpecificEnergyDensity_gatedVariation m hmeas).comp
    measurableEmbedding_swapGrids.measurable
  have hEq : ((fun p : CoupledSpace =>
        rootedSpecificEnergyDensity (decode p.1) (gatedVariation m p) 0) ∘ swapGrids)
      = fun p : CoupledSpace =>
        rootedSpecificEnergyDensity (decode p.1) (gatedVariation m (swapGrids p)) 0 := by
    funext p
    rfl
  rw [hEq] at h
  exact h

theorem lintegral_rootedSpecificEnergyDensity_swappedVariation_ne_top (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν) (m : ℕ) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (gatedVariation m (swapGrids p)) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞ := by
  have h : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (gatedVariation m (swapGrids p)) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (gatedVariation m p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure)) :=
    (measurePreserving_swapGrids ν).lintegral_comp
      (measurable_rootedSpecificEnergyDensity_gatedVariation m hmeas)
  rw [h]
  exact lintegral_rootedSpecificEnergyDensity_gatedVariation_ne_top ν hν hFE hmeas hproj m

/-- The stage error of the passive grid, as a coupled field. -/
noncomputable def passiveError (ms : ℕ → ℕ) (m : ℕ) (p : CoupledSpace) : Vertex p.1.val → Plane :=
  fun v => phi (decode p.1) p.2.2 m v - crossPotential ms p v

/-- The stage error of the block grid, as a coupled field. -/
noncomputable def blockError (ms : ℕ → ℕ) (m : ℕ) (p : CoupledSpace) : Vertex p.1.val → Plane :=
  fun v => phi (decode p.1) p.2.1 m v - blockPotential ms p v

theorem rootedSpecificEnergyDensity_passiveError (ms : ℕ → ℕ) (m : ℕ) (p : CoupledSpace) :
    rootedSpecificEnergyDensity (decode p.1) (passiveError ms m p) 0
      = markedSpecificGradientError ms m (passiveMarked p) := rfl

theorem rootedSpecificEnergyDensity_blockError (ms : ℕ → ℕ) (m : ℕ) (p : CoupledSpace) :
    rootedSpecificEnergyDensity (decode p.1) (blockError ms m p) 0
      = markedSpecificGradientError ms m (blockMarked p) := rfl

theorem aemeasurable_rootedSpecificEnergyDensity_passiveError (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    AEMeasurable (fun p : CoupledSpace =>
      rootedSpecificEnergyDensity (decode p.1) (passiveError ms m p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  have hsub : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      p.1 ∈ SublinearEvent :=
    ae_coupled_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)
  refine (MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (Prod.fst : CoupledSpace → Env)) measurable_fst (Ψ := passiveErrorLabel ms m)
    (measurable_passiveErrorLabel ms m hmeas)).aemeasurable.congr ?_
  filter_upwards [hsub] with p hG
  show rootedSpecificEnergyDensity (decode p.1)
      (fun v : Vertex p.1.val => passiveErrorLabel ms m p v.val) 0
    = rootedSpecificEnergyDensity (decode p.1) (passiveError ms m p) 0
  unfold passiveError
  rw [passiveError_eq_label ms m hG]

theorem aemeasurable_rootedSpecificEnergyDensity_blockError (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    AEMeasurable (fun p : CoupledSpace =>
      rootedSpecificEnergyDensity (decode p.1) (blockError ms m p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  have hsub : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      p.1 ∈ SublinearEvent :=
    ae_coupled_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)
  refine (MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (Prod.fst : CoupledSpace → Env)) measurable_fst (Ψ := blockErrorLabel ms m)
    (measurable_blockErrorLabel ms m hmeas)).aemeasurable.congr ?_
  filter_upwards [hsub] with p hG
  show rootedSpecificEnergyDensity (decode p.1)
      (fun v : Vertex p.1.val => blockErrorLabel ms m p v.val) 0
    = rootedSpecificEnergyDensity (decode p.1) (blockError ms m p) 0
  unfold blockError
  rw [blockError_eq_label ms m hG]

/-- The expected specific energy of the passive stage error is the marked-law gradient error. -/
theorem lintegral_rootedSpecificEnergyDensity_passiveError (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (passiveError ms m p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ ω, markedSpecificGradientError ms m ω ∂(ν.prod gridMeasure) := by
  have h := lintegral_comp_passiveMarked ν (markedSpecificGradientError ms m)
    (aemeasurable_markedSpecificGradientError ν hν hFE.ne ms hmeas m)
  rw [← h]
  refine lintegral_congr fun p => ?_
  exact rootedSpecificEnergyDensity_passiveError ms m p

theorem lintegral_rootedSpecificEnergyDensity_blockError (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (blockError ms m p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ ω, markedSpecificGradientError ms m ω ∂(ν.prod gridMeasure) := by
  have h := lintegral_comp_blockMarked ν (markedSpecificGradientError ms m)
    (aemeasurable_markedSpecificGradientError ν hν hFE.ne ms hmeas m)
  rw [← h]
  refine lintegral_congr fun p => ?_
  exact rootedSpecificEnergyDensity_blockError ms m p

theorem lintegral_markedSpecificGradientError_ne_top (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (m : ℕ) :
    (∫⁻ ω, markedSpecificGradientError ms m ω ∂(ν.prod gridMeasure)) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_
    (SpecificEnergyConvergence.lintegral_markedSpecificGradientError_le_sub_iInf ν hν hFE hmeas
      hproj ms hms hconv m)
  exact ne_top_of_le_ne_top
    (SpecificEnergyConvergence.markedStageEnergy_lt_top ν hν hFE hproj m).ne tsub_le_self

/-- The copy difference `Φ² − Φ¹`, as a coupled field. -/
noncomputable def copyDifference (ms : ℕ → ℕ) (p : CoupledSpace) : Vertex p.1.val → Plane :=
  fun v => crossPotential ms p v - blockPotential ms p v

theorem measurable_rootedSpecificEnergyDensity_copyDifference (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable fun p : CoupledSpace =>
      rootedSpecificEnergyDensity (decode p.1) (copyDifference ms p) 0 := by
  have h := MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (Prod.fst : CoupledSpace → Env)) measurable_fst
    (Ψ := fun p n => crossLabel ms p n - blockLabel ms p n)
    (fun n => (measurable_crossLabel ms hmeas n).sub (measurable_blockLabel ms hmeas n))
  exact h

theorem lintegral_rootedSpecificEnergyDensity_copyDifference_ne_top (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (copyDifference ms p) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞ := by
  have hle : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (copyDifference ms p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure)))
      ≤ ∫⁻ p, (2 * rootedSpecificEnergyDensity (decode p.1) (crossPotential ms p) 0
          + 2 * rootedSpecificEnergyDensity (decode p.1) (blockPotential ms p) 0)
          ∂(ν.prod (gridMeasure.prod gridMeasure)) :=
    lintegral_mono fun p => MarkedStageCoefficientScaling.rootedSpecificEnergyDensity_sub_le
      (decode p.1) (decode_geometry p.1) (crossPotential ms p) (blockPotential ms p) 0
  rw [lintegral_add_left'
      ((measurable_rootedSpecificEnergyDensity_crossPotential ms hmeas).const_mul 2).aemeasurable,
    lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)] at hle
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by norm_num)
      (lintegral_rootedSpecificEnergyDensity_crossPotential_ne_top ν hν hFE ms hms hmeas hproj
        hconv),
      ENNReal.mul_ne_top (by norm_num)
      (lintegral_rootedSpecificEnergyDensity_blockPotential_ne_top ν hν hFE ms hms hmeas hproj
        hconv)⟩) hle

/-! ### Integrability and measurability of the five pairings -/

theorem integrable_pairing_variation (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (m : ℕ) :
    Integrable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  refine integrable_rootedPairingDensity (ν.prod (gridMeasure.prod gridMeasure))
    (fun p : CoupledSpace => decode p.1) (blockPotential ms) (gatedVariation m)
    (fun _ => (0 : Plane)) (fun p => decode_geometry p.1)
    (measurable_rootedSpecificEnergyDensity_blockPotential ms hmeas).aemeasurable
    (measurable_rootedSpecificEnergyDensity_gatedVariation m hmeas).aemeasurable ?_
    (lintegral_rootedSpecificEnergyDensity_blockPotential_ne_top ν hν hFE ms hms hmeas hproj hconv)
    (lintegral_rootedSpecificEnergyDensity_gatedVariation_ne_top ν hν hFE hmeas hproj m)
  have h := measurable_rootedPairingDensity_of_labels (E := (Prod.fst : CoupledSpace → Env))
    measurable_fst (measurable_blockLabel ms hmeas) (measurable_variationLabel m hmeas)
  have hEq : (fun p : CoupledSpace => rootedPairingDensity (decode p.1)
        (fun v : Vertex p.1.val => blockLabel ms p v.val)
        (fun v : Vertex p.1.val => variationLabel m p v.val) 0)
      = fun p : CoupledSpace =>
        rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m p) 0 := by
    funext p
    rw [gatedVariation_eq_label_field m p]
    rfl
  rw [hEq] at h
  exact h.aestronglyMeasurable

theorem integrable_pairing_swappedVariation (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (m : ℕ) :
    Integrable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m (swapGrids p)) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  refine integrable_rootedPairingDensity (ν.prod (gridMeasure.prod gridMeasure))
    (fun p : CoupledSpace => decode p.1) (blockPotential ms)
    (fun p => gatedVariation m (swapGrids p))
    (fun _ => (0 : Plane)) (fun p => decode_geometry p.1)
    (measurable_rootedSpecificEnergyDensity_blockPotential ms hmeas).aemeasurable
    (measurable_rootedSpecificEnergyDensity_swappedVariation m hmeas).aemeasurable ?_
    (lintegral_rootedSpecificEnergyDensity_blockPotential_ne_top ν hν hFE ms hms hmeas hproj hconv)
    (lintegral_rootedSpecificEnergyDensity_swappedVariation_ne_top ν hν hFE hmeas hproj m)
  have h := measurable_rootedPairingDensity_of_labels (E := (Prod.fst : CoupledSpace → Env))
    measurable_fst (measurable_blockLabel ms hmeas)
    (LH := fun p n => variationLabel m (swapGrids p) n)
    (fun n => (measurable_variationLabel m hmeas n).comp measurableEmbedding_swapGrids.measurable)
  have hEq : (fun p : CoupledSpace => rootedPairingDensity (decode p.1)
        (fun v : Vertex p.1.val => blockLabel ms p v.val)
        (fun v : Vertex p.1.val => variationLabel m (swapGrids p) v.val) 0)
      = fun p : CoupledSpace =>
        rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m (swapGrids p)) 0 := by
    funext p
    rw [gatedVariation_eq_label_field m (swapGrids p)]
    rfl
  rw [hEq] at h
  exact h.aestronglyMeasurable

theorem aestronglyMeasurable_pairing_passiveError (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    AEStronglyMeasurable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (passiveError ms m p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  have hsub : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      p.1 ∈ SublinearEvent :=
    ae_coupled_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)
  have h := measurable_rootedPairingDensity_of_labels (E := (Prod.fst : CoupledSpace → Env))
    measurable_fst (measurable_blockLabel ms hmeas) (measurable_passiveErrorLabel ms m hmeas)
  refine h.aestronglyMeasurable.congr ?_
  filter_upwards [hsub] with p hG
  show rootedPairingDensity (decode p.1) (fun v : Vertex p.1.val => blockLabel ms p v.val)
      (fun v : Vertex p.1.val => passiveErrorLabel ms m p v.val) 0
    = rootedPairingDensity (decode p.1) (blockPotential ms p) (passiveError ms m p) 0
  unfold passiveError
  rw [passiveError_eq_label ms m hG]
  rfl

theorem aestronglyMeasurable_pairing_blockError (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (m : ℕ) :
    AEStronglyMeasurable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms m p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  have hsub : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      p.1 ∈ SublinearEvent :=
    ae_coupled_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)
  have h := measurable_rootedPairingDensity_of_labels (E := (Prod.fst : CoupledSpace → Env))
    measurable_fst (measurable_blockLabel ms hmeas) (measurable_blockErrorLabel ms m hmeas)
  refine h.aestronglyMeasurable.congr ?_
  filter_upwards [hsub] with p hG
  show rootedPairingDensity (decode p.1) (fun v : Vertex p.1.val => blockLabel ms p v.val)
      (fun v : Vertex p.1.val => blockErrorLabel ms m p v.val) 0
    = rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms m p) 0
  unfold blockError
  rw [blockError_eq_label ms m hG]
  rfl

theorem integrable_pairing_passiveError (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (m : ℕ) :
    Integrable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (passiveError ms m p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  refine integrable_rootedPairingDensity (ν.prod (gridMeasure.prod gridMeasure))
    (fun p : CoupledSpace => decode p.1) (blockPotential ms) (passiveError ms m)
    (fun _ => (0 : Plane)) (fun p => decode_geometry p.1)
    (measurable_rootedSpecificEnergyDensity_blockPotential ms hmeas).aemeasurable
    (aemeasurable_rootedSpecificEnergyDensity_passiveError ν hν hFE ms hmeas m)
    (aestronglyMeasurable_pairing_passiveError ν hν hFE ms hmeas m)
    (lintegral_rootedSpecificEnergyDensity_blockPotential_ne_top ν hν hFE ms hms hmeas hproj hconv)
    ?_
  rw [lintegral_rootedSpecificEnergyDensity_passiveError ν hν hFE ms hmeas m]
  exact lintegral_markedSpecificGradientError_ne_top ν hν hFE ms hms hmeas hproj hconv m

theorem integrable_pairing_blockError (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (m : ℕ) :
    Integrable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms m p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  refine integrable_rootedPairingDensity (ν.prod (gridMeasure.prod gridMeasure))
    (fun p : CoupledSpace => decode p.1) (blockPotential ms) (blockError ms m)
    (fun _ => (0 : Plane)) (fun p => decode_geometry p.1)
    (measurable_rootedSpecificEnergyDensity_blockPotential ms hmeas).aemeasurable
    (aemeasurable_rootedSpecificEnergyDensity_blockError ν hν hFE ms hmeas m)
    (aestronglyMeasurable_pairing_blockError ν hν hFE ms hmeas m)
    (lintegral_rootedSpecificEnergyDensity_blockPotential_ne_top ν hν hFE ms hms hmeas hproj hconv)
    ?_
  rw [lintegral_rootedSpecificEnergyDensity_blockError ν hν hFE ms hmeas m]
  exact lintegral_markedSpecificGradientError_ne_top ν hν hFE ms hms hmeas hproj hconv m

theorem aestronglyMeasurable_pairing_copyDifference (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    AEStronglyMeasurable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (copyDifference ms p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := by
  have h := measurable_rootedPairingDensity_of_labels (E := (Prod.fst : CoupledSpace → Env))
    measurable_fst (measurable_blockLabel ms hmeas)
    (LH := fun p n => crossLabel ms p n - blockLabel ms p n)
    (fun n => (measurable_crossLabel ms hmeas n).sub (measurable_blockLabel ms hmeas n))
  exact h.aestronglyMeasurable

theorem integrable_pairing_copyDifference (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) :
    Integrable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (copyDifference ms p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) :=
  integrable_rootedPairingDensity (ν.prod (gridMeasure.prod gridMeasure))
    (fun p : CoupledSpace => decode p.1) (blockPotential ms) (copyDifference ms)
    (fun _ => (0 : Plane)) (fun p => decode_geometry p.1)
    (measurable_rootedSpecificEnergyDensity_blockPotential ms hmeas).aemeasurable
    (measurable_rootedSpecificEnergyDensity_copyDifference ms hmeas).aemeasurable
    (aestronglyMeasurable_pairing_copyDifference ν ms hmeas)
    (lintegral_rootedSpecificEnergyDensity_blockPotential_ne_top ν hν hFE ms hms hmeas hproj hconv)
    (lintegral_rootedSpecificEnergyDensity_copyDifference_ne_top ν hν hFE ms hms hmeas hproj hconv)

/-! ### The expected pairings along the stages -/

/-- The almost-sure decomposition, with the error and difference fields named. -/
theorem ae_pairing_decomposition (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (m : ℕ) :
    ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m (swapGrids p)) 0
          - rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m p) 0
        = rootedPairingDensity (decode p.1) (blockPotential ms p) (passiveError ms m p) 0
          - (rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms m p) 0
            - rootedPairingDensity (decode p.1) (blockPotential ms p) (copyDifference ms p) 0) := by
  have hgood : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)), p.1 ∈ goodSet :=
    ae_coupled_of_ae_env ν (ae_mem_goodSet ν hν hFE.ne)
  filter_upwards [hgood] with p hg
  exact pairing_decomposition ms m p (gatedVariation_eq_phi_sub m (p := swapGrids p) hg)
    (gatedVariation_eq_phi_sub m hg)

/-- **`E⟪Φ¹, Φ² − Φ¹⟫ = E⟪Φ¹, φ_m¹ − Φ¹⟫ − E⟪Φ¹, φ_m² − Φ²⟫` at every positive stage.** -/
theorem integral_crossPairing_eq_stage (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (m : ℕ) (hm : m ≠ 0) :
    (∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (copyDifference ms p) 0
          ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = (∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms m p) 0
            ∂(ν.prod (gridMeasure.prod gridMeasure)))
        - ∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (passiveError ms m p) 0
            ∂(ν.prod (gridMeasure.prod gridMeasure)) := by
  have hPV := integrable_pairing_variation ν hν hFE ms hms hmeas hproj hconv m
  have hPW := integrable_pairing_swappedVariation ν hν hFE ms hms hmeas hproj hconv m
  have hPA := integrable_pairing_passiveError ν hν hFE ms hms hmeas hproj hconv m
  have hPB := integrable_pairing_blockError ν hν hFE ms hms hmeas hproj hconv m
  have hPK := integrable_pairing_copyDifference ν hν hFE ms hms hmeas hproj hconv
  have hYZ : Integrable (fun p : CoupledSpace =>
      rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms m p) 0
        - rootedPairingDensity (decode p.1) (blockPotential ms p) (copyDifference ms p) 0)
      (ν.prod (gridMeasure.prod gridMeasure)) := hPB.sub hPK
  have hWzero := integral_swappedCrossPairing_eq_zero ν hν hFE ms hms hmeas hproj hconv hpatch m hm
  have hVzero := integral_blockPairing_eq_zero ν hν hFE ms hms hmeas hproj hconv hpatch m hm
  have hL : (∫ p, (rootedPairingDensity (decode p.1) (blockPotential ms p)
        (gatedVariation m (swapGrids p)) 0
      - rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m p) 0)
        ∂(ν.prod (gridMeasure.prod gridMeasure))) = 0 := by
    rw [integral_sub hPW hPV, hWzero, hVzero, sub_zero]
  have hR : (∫ p, (rootedPairingDensity (decode p.1) (blockPotential ms p)
        (gatedVariation m (swapGrids p)) 0
      - rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m p) 0)
        ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = (∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (passiveError ms m p) 0
            ∂(ν.prod (gridMeasure.prod gridMeasure)))
        - ((∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms m p) 0
              ∂(ν.prod (gridMeasure.prod gridMeasure)))
          - ∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (copyDifference ms p) 0
              ∂(ν.prod (gridMeasure.prod gridMeasure))) := by
    rw [integral_congr_ae (ae_pairing_decomposition ν hν hFE ms m), integral_sub hPA hYZ,
      integral_sub hPB hPK]
  rw [hL] at hR
  linarith

/-- **The limit: the expected cross pairing `E⟪Φ¹, Φ² − Φ¹⟫` vanishes.** -/
theorem integral_crossPairing_eq_zero_limit (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms) :
    (∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (copyDifference ms p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure))) = 0 := by
  have hspec := SpecificEnergyConvergence.markedSpecificEnergyConvergence_of_nestedProjection ν hν
    hFE hmeas hproj ms hms hconv
  have hθfin := lintegral_rootedSpecificEnergyDensity_blockPotential_ne_top ν hν hFE ms hms hmeas
    hproj hconv
  have hAtend : Tendsto (fun n : ℕ => ∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
      (passiveError ms n p) 0 ∂(ν.prod (gridMeasure.prod gridMeasure))) atTop (𝓝 0) := by
    have hEq : (fun n : ℕ => ∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
          (passiveError ms n p) 0 ∂(ν.prod (gridMeasure.prod gridMeasure)))
        = fun n : ℕ => ∫⁻ ω, markedSpecificGradientError ms n ω ∂(ν.prod gridMeasure) :=
      funext fun n => lintegral_rootedSpecificEnergyDensity_passiveError ν hν hFE ms hmeas n
    rw [hEq]
    exact hspec.2
  have hBtend : Tendsto (fun n : ℕ => ∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
      (blockError ms n p) 0 ∂(ν.prod (gridMeasure.prod gridMeasure))) atTop (𝓝 0) := by
    have hEq : (fun n : ℕ => ∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
          (blockError ms n p) 0 ∂(ν.prod (gridMeasure.prod gridMeasure)))
        = fun n : ℕ => ∫⁻ ω, markedSpecificGradientError ms n ω ∂(ν.prod gridMeasure) :=
      funext fun n => lintegral_rootedSpecificEnergyDensity_blockError ν hν hFE ms hmeas n
    rw [hEq]
    exact hspec.2
  have hI := tendsto_integral_rootedPairingDensity_of_tendsto_zero
    (ν.prod (gridMeasure.prod gridMeasure)) (fun p : CoupledSpace => decode p.1)
    (blockPotential ms) (passiveError ms) (fun _ => (0 : Plane)) (fun p => decode_geometry p.1)
    (measurable_rootedSpecificEnergyDensity_blockPotential ms hmeas).aemeasurable
    (fun n => aemeasurable_rootedSpecificEnergyDensity_passiveError ν hν hFE ms hmeas n)
    (fun n => aestronglyMeasurable_pairing_passiveError ν hν hFE ms hmeas n) hθfin hAtend
  have hJ := tendsto_integral_rootedPairingDensity_of_tendsto_zero
    (ν.prod (gridMeasure.prod gridMeasure)) (fun p : CoupledSpace => decode p.1)
    (blockPotential ms) (blockError ms) (fun _ => (0 : Plane)) (fun p => decode_geometry p.1)
    (measurable_rootedSpecificEnergyDensity_blockPotential ms hmeas).aemeasurable
    (fun n => aemeasurable_rootedSpecificEnergyDensity_blockError ν hν hFE ms hmeas n)
    (fun n => aestronglyMeasurable_pairing_blockError ν hν hFE ms hmeas n) hθfin hBtend
  have hconst : (fun _ : ℕ => ∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p)
        (copyDifference ms p) 0 ∂(ν.prod (gridMeasure.prod gridMeasure)))
      =ᶠ[atTop] fun n : ℕ =>
        (∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms n p) 0
            ∂(ν.prod (gridMeasure.prod gridMeasure)))
        - ∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (passiveError ms n p) 0
            ∂(ν.prod (gridMeasure.prod gridMeasure)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact integral_crossPairing_eq_stage ν hν hFE ms hms hmeas hproj hconv hpatch n hn.ne'
  have hlim : Tendsto (fun n : ℕ =>
      (∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (blockError ms n p) 0
          ∂(ν.prod (gridMeasure.prod gridMeasure)))
      - ∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (passiveError ms n p) 0
          ∂(ν.prod (gridMeasure.prod gridMeasure))) atTop (𝓝 (0 - 0)) := hJ.sub hI
  have huniq := tendsto_nhds_unique (tendsto_const_nhds.congr' hconst) hlim
  rw [sub_zero] at huniq
  exact huniq


/-! ### `hzero` -/

/-- **`horth`: the cross orthogonality `∫ ⟪∇θ¹, ∇(θ² − θ¹)⟫ = 0`**, in the shape of
`Corrector/CopyDifferenceInputReduction`. -/
theorem integral_rootedPairing_cross_eq_zero (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms) :
    (∫ p, rootedPairing (firstPotential ms)
      (fun q u => secondPotential ms q u - firstPotential ms q u) p
        ∂ν.prod (gridLaw.prod gridLaw)) = 0 := by
  have h := integral_crossPairing_eq_zero_limit ν hν hFE ms hms hmeas hproj hconv hpatch
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p =>
    rootedSpecificPairingDensity_eq_rootedPairingDensity (decode p.1) (blockPotential ms p)
      (copyDifference ms p) 0)

/-- **`hi`: the cross pairing is integrable.** -/
theorem integrable_rootedPairing_cross (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) :
    Integrable (rootedPairing (firstPotential ms)
      fun q u => secondPotential ms q u - firstPotential ms q u)
      (ν.prod (gridLaw.prod gridLaw)) := by
  have hPK := integrable_pairing_copyDifference ν hν hFE ms hms hmeas hproj hconv
  exact hPK.congr (Filter.Eventually.of_forall fun p =>
    (rootedSpecificPairingDensity_eq_rootedPairingDensity (decode p.1) (blockPotential ms p)
      (copyDifference ms p) 0).symm)

/-- **`hzero`, DISCHARGED**: the expected rooted specific-energy density at the origin of the
difference of the two grid-copy potentials vanishes. -/
theorem originEnergy_eq_zero (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
        (fun u => firstPotential ms p u - secondPotential ms p u) 0
          ∂ν.prod (gridLaw.prod gridLaw)) = 0 :=
  CopyDifferenceOriginEnergy.originEnergy_eq_zero_of_cross_orthogonality ν ms
    (integrable_rootedPairing_cross ν hν hFE ms hms hmeas hproj hconv)
    (integral_rootedPairing_cross_eq_zero ν hν hFE ms hms hmeas hproj hconv hpatch)

/-! ### The harmonic-coordinate theorem's count -/

/-- **The harmonic-coordinate reduction to `hmeas` and `hproj`.**  Along the subsequence that
`hproj` produces, the two-grid auxiliary space gives `hconv` and `hpatch` from `hmeas`, and
`hzero` is then a theorem. -/
theorem harmonicCoordinateConclusions_of_two_inputs (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν) :
    HarmonicCoordinateConclusions ν := by
  obtain ⟨ms, hms, hgeom⟩ :=
    SpecificEnergyConvergence.exists_strictMono_geometric_markedStageDefect ν hν hFE hproj
  have hmax : StageDifferenceWeakMaximal.MarkedStageDifferenceWeakMaximal ν :=
    AuxiliaryGridMarkedSpace.markedStageDifferenceWeakMaximal_auxTwoGrid ν hν hFE hmeas
  have hconv : MarkedDifferencesConverge ν ms :=
    MarkedDifferenceIncrementsFromMaximal.markedDifferencesConverge_of_stageDifferenceWeakMaximal
      ν hν hFE ms hms hgeom hmax
  have hpatch : MarkedPatchConvergence ν ms :=
    StageDifferenceWeakMaximal.markedPatchConvergence_of_stageDifferenceWeakMaximal ν hν hFE
      ms hms hgeom hmax hconv
  exact HarmonicCoordinateThreeInputs.harmonicCoordinateConclusions_of_rate_and_originEnergy ν hν
    hFE ms hms hgeom hmeas
    (SpecificEnergyConvergence.markedSpecificEnergyConvergence_of_nestedProjection ν hν hFE hmeas
      hproj ms hms hconv)
    (originEnergy_eq_zero ν hν hFE ms hms hmeas hproj hconv hpatch)

/-- **The harmonic-coordinate reduction to `hproj` alone**, with `hmeas` discharged by
`Corrector/BlockInterpolantSelectionCandidate.measurable_gatedApproximant`. -/
theorem harmonicCoordinateConclusions_of_projection (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν) :
    HarmonicCoordinateConclusions ν :=
  harmonicCoordinateConclusions_of_two_inputs ν hν hFE
    BlockInterpolantSelectionCandidate.measurable_gatedApproximant hproj

end Limit

/-- The same at the main theorem's own law `validLaw P hP`. -/
theorem harmonicCoordinateConclusions_validLaw_of_projection (P : Measure RawCode)
    [IsProbabilityMeasure P] (hP : SupportedOnValid P) (hmt : AmbientMassTransport P hP)
    (hFE : FiniteEnergyMoment (validLaw P hP))
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound (validLaw P hP)) :
    HarmonicCoordinateConclusions (validLaw P hP) :=
  harmonicCoordinateConclusions_of_projection (validLaw P hP) hmt hFE hproj

end ReflectedGMS.CopyDifferenceOrthogonalityLimit
