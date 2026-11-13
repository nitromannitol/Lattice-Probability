/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StageBlockEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageBlockEnergyActiveEdges
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StagePairingVanishing
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedStageCoefficientScaling
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRootedSpecificEnergyMeasurability

/-!
# `hproj` is CLOSED: the two block-local inputs of `Corrector/StagePairingVanishing`

`Corrector/StagePairingVanishing.markedNestedProjectionBound_of_blockData` produces
`SpecificEnergyConvergence.MarkedNestedProjectionBound ν` (the assembly input `hproj`) from
`s:eq:MTP`, the (FE) moment and two block-local statements: `MarkedStageBlockEnergy ν` (the
long-standing `hmE`) and `MarkedStagePairingEndpointFinite ν`.  This module proves both, with no
further hypothesis, so `hproj` is a theorem.

## The route, and why it is not circular

Write `b = φ_0` for the centroid embedding and `v_m = b − φ_m` for the variation of stage `m`
(the gated field `stageDifferenceField 0 m`), which vanishes on `skel_m`
(`var_eq_zero_on_skeleton`), hence on `skel_k` for every `k ≥ m`.

* **(A) every stage has finite specific energy, without the projection bound.**  Pointwise
  `ρ(φ_m) = ρ(b − v_m) ≤ 2ρ(b) + 2ρ(v_m)`, so it suffices to bound `V_m := E ρ(v_m)`.  The
  endpoint density of the energy coefficient `c_e|∇_e v_m|²` is exactly `ρ(v_m)`
  (`StageEnergyRedistributionField.energyEndpointDensity_eq_rootedSpecificEnergyDensity`), and
  the checked redistribution `s:lem:redistribution` — run for the positive part of the pairing
  coefficient of `(v_m, v_m)` at parameter `m`, an honest `PairingOwnership` because `v_m` vanishes
  on `skel_m` — turns `V_m` into the expected owner-block density `E[ℓ(S_m(0))⁻² A_{S_m(0)}(v_m)]`
  of the active-edge energy of `v_m`.  The active-edge Pythagoras
  (`StageBlockEnergyActiveEdges.activeEnergySum_sub_le`, from the blockwise minimality of `φ_m`
  on `S_m(0)`) bounds `A_S(v_m) ≤ A_S(b)`, and a second redistribution — for the owned energy
  field of `b`, which needs no vanishing on the skeleton — sends `E[ℓ⁻² A_{S_m(0)}(b)]` back to an
  endpoint density dominated by `ρ(b)`.  So `V_m ≤ e_0 < ∞` (`s:lem:e0`) and
  `e_m ≤ 2e_0 + 2V_m < ∞`.  Nothing here uses `MarkedNestedProjectionBound`.
* **(B) `hmE`.**  The same redistribution for `(v_m, v_m)` at parameter `n ≥ m` (again a
  `PairingOwnership`, since `skel_n ⊆ skel_m`) shows `E[ℓ(S_n(0))⁻² A_{S_n(0)}(v_m)] = V_m < ∞`; the
  owner-block density is almost surely measurable
  (`StageEnergyRedistributionField.aemeasurable_ownerBlockDensity`), so almost surely
  `A_{S_n(0)}(v_m) < ∞`, which is the full block energy of `v_m` because its non-active energy
  vanishes.  With the block energy of `b` (`s:eq:Wbound`), `φ_m = b − v_m` has finite energy on
  the patch of `S_n(0)`.
* **(C) the endpoint densities.**  Termwise `|c_e⟪∇_e φ_n, ∇_e(φ_m − φ_n)⟫| ≤ c_e|∇_e φ_n|² +
  c_e|∇_e(φ_m − φ_n)|²`, so both endpoint densities are dominated by `ρ(φ_n) + ρ(φ_m − φ_n)`,
  whose expectation is `e_n + ‖g_m − g_n‖_*² ≤ e_n + 2e_m + 2e_n < ∞` by (A).

## What is proved

* `gatedStageEnergy_lt_top` / `markedStageEnergy_ne_top` — **(A)**, the non-circular `hfin`.
* `markedStageBlockEnergy` — **`MarkedStageBlockEnergy ν`**, i.e. `hmE`.
* `markedStagePairingEndpointFinite` — **`MarkedStagePairingEndpointFinite ν`**.
* `markedNestedProjectionBound` — **`hproj`**, from `MassTransport ν` and
  `FiniteEnergyMoment ν` alone; `markedStagePairingVanishes` and
  `markedSpecificEnergyConvergence_of_conv` are the two other consumers of the block data.

Every hypothesis is stated at `decode e` data; no `Summable` over cells and no finite total
energy of the environment is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StageBlockEnergy

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedStageFieldCovariance MarkedBlockAveraging DiameterBlockIndex
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open OwnedFieldPairingTransport PairingOwnershipInstance NestedProjectionProducers
open ActualMarkedBlockTransport OwnedFieldLabelTransport StagePairingBlockOwnership
open StagePairingSkeletonData PatchCentroidTraceFiniteEnergy StagePairingVanishing
open StageEnergyRedistributionField StageBlockEnergyActiveEdges

/-! ### Pointwise identities of the gated stage fields -/

/-- `φ_m = φ_0 − (φ_0 − φ_m)` at every marked configuration. -/
theorem stageField_eq_sub_var (m : ℕ) (ω : MarkedEnvironment) :
    stageField m ω = fun v => stageField 0 ω v - stageDifferenceField 0 m ω v := by
  funext v
  show stageField m ω v = stageField 0 ω v - (stageField 0 ω v - stageField m ω v)
  rw [sub_sub_cancel]

/-- **The variation `φ_0 − φ_m` vanishes on `skel_k` for every `k ≥ m`, `k ≠ 0`.**  Both
`φ_0` and `φ_m` agree with `φ_k` there (`stageDifferenceField_eq_zero_on_skeleton'`). -/
theorem var_eq_zero_on_skeleton (m : ℕ) {k : ℕ} (hmk : m ≤ k) (hk : k ≠ 0)
    (ω : MarkedEnvironment) {v : Vertex ω.1.val}
    (hv : v ∈ skeleton (decode ω.1) ω.2 (k : ℝ)) :
    stageDifferenceField 0 m ω v = 0 := by
  have h1 := stageDifferenceField_eq_zero_on_skeleton' (Nat.zero_le k) hk ω hv
  have h2 := stageDifferenceField_eq_zero_on_skeleton' hmk hk ω hv
  have e1 : stageField 0 ω v = stageField k ω v :=
    sub_eq_zero.1 (show stageField 0 ω v - stageField k ω v = 0 from h1)
  have e2 : stageField m ω v = stageField k ω v :=
    sub_eq_zero.1 (show stageField m ω v - stageField k ω v = 0 from h2)
  show stageField 0 ω v - stageField m ω v = 0
  rw [e1, e2, sub_self]

/-- Where the selected squares at a positive parameter fail to cover the plane, the environment
is off the good event and the variation vanishes identically. -/
theorem var_cover_or_vanish (m : ℕ) {k : ℕ} (hk : k ≠ 0) (ω : MarkedEnvironment)
    (hcov : ¬ SelectionCoversOn (decode ω.1) ω.2 (k : ℝ)) (v : Vertex ω.1.val) :
    stageDifferenceField 0 m ω v = 0 := by
  by_cases hG : ω.1 ∈ SublinearEvent
  · exact absurd (selectionCoversOn_of_mem_sublinearEvent hG ω.2
      (by exact_mod_cast Nat.pos_of_ne_zero hk : (0 : ℝ) < (k : ℝ))) hcov
  · exact stageDifferenceField_eq_zero_of_notMem 0 m hG v

/-- The ownership datum of the pair `(v_m, v_m)` at any parameter `k ≥ m`, `k ≠ 0`. -/
noncomputable def varOwnership (m : ℕ) {k : ℕ} (hmk : m ≤ k) (hk : k ≠ 0) :
    PairingOwnership actualReRooting (k : ℝ) (stageDifferenceField 0 m)
      (stageDifferenceField 0 m) :=
  gatedPairingOwnership actualReRooting (k : ℝ) (stageDifferenceField 0 m)
    (stageDifferenceField 0 m)
    (fun ω hcov v => var_cover_or_vanish m hk ω hcov v)
    (fun ω v hv => var_eq_zero_on_skeleton m hmk hk ω hv)

theorem varOwnership_owner (m : ℕ) {k : ℕ} (hmk : m ≤ k) (hk : k ≠ 0) (ω : MarkedEnvironment)
    (q : ℕ × ℕ) :
    (posField (varOwnership m hmk hk)).owner ω q = labelOwner actualReRooting (k : ℝ) ω q := rfl

theorem varOwnership_weight (m : ℕ) {k : ℕ} (hmk : m ≤ k) (hk : k ≠ 0) (ω : MarkedEnvironment)
    (p : ℕ × ℕ) :
    (posField (varOwnership m hmk hk)).weight ω p
      = ENNReal.ofReal (pairCoeff ω.1 (stageDifferenceField 0 m ω) (stageDifferenceField 0 m ω) p) :=
  rfl

/-! ### Measurability of the two energy coefficients -/

theorem measurable_pairCoeff_var (m : ℕ) (q : ℕ × ℕ) :
    Measurable fun ω : MarkedEnvironment =>
      pairCoeff ω.1 (stageDifferenceField 0 m ω) (stageDifferenceField 0 m ω) q := by
  have hL : ∀ n : ℕ, Measurable fun ω : MarkedEnvironment =>
      gatedApproximant 0 ω n - gatedApproximant m ω n := fun n =>
    (BlockInterpolantSelectionCandidate.measurable_gatedApproximant 0 n).sub
      (BlockInterpolantSelectionCandidate.measurable_gatedApproximant m n)
  exact measurable_pairCoeff_of_labels (E := fun ω : MarkedEnvironment => ω.1) measurable_fst
    hL hL q

theorem measurable_pairCoeff_base (q : ℕ × ℕ) :
    Measurable fun ω : MarkedEnvironment => pairCoeff ω.1 (stageField 0 ω) (stageField 0 ω) q :=
  measurable_pairCoeff_of_labels (E := fun ω : MarkedEnvironment => ω.1) measurable_fst
    (fun n => BlockInterpolantSelectionCandidate.measurable_gatedApproximant 0 n)
    (fun n => BlockInterpolantSelectionCandidate.measurable_gatedApproximant 0 n) q

/-- Measurability of the rooted specific-energy density of a stage field. -/
theorem measurable_rootedSpecificEnergyDensity_stageField (m : ℕ) :
    Measurable fun ω : MarkedEnvironment =>
      rootedSpecificEnergyDensity (decode ω.1) (stageField m ω) 0 :=
  MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := fun ω : MarkedEnvironment => ω.1) measurable_fst
    (Ψ := fun ω n => gatedApproximant m ω n)
    (fun n => BlockInterpolantSelectionCandidate.measurable_gatedApproximant m n)

/-! ### The almost-sure events -/

theorem ae_good (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) :
    ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw), ω.1 ∈ SublinearEvent :=
  ae_marked_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)

theorem ae_cellBounds (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) :
    ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw), SpatialDiameterCellBounds (decode ω.1) :=
  ae_marked_of_ae_env ν (SpatialMaximalForFiniteEnergy.ae_spatialDiameterCellBounds ν hν hFE.ne)

theorem ae_bdry (ν : Measure Env) [IsProbabilityMeasure ν] (hν : MassTransport ν) :
    ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw), (0 : Plane) ∉ boundaryMask (decode ω.1) :=
  ae_notMem_boundaryMask_env actualReRooting
    (PairingTransportWeld.massTransport_map_env_prod ν hν) measurable_fst

/-! ### The stage defect is dominated by the two stage energies -/

/-- `‖g_m − g_n‖_*² ≤ 2 e_m + 2 e_n` for the gated stage energies. -/
theorem gatedStageDefect_le (ν : Measure Env) [SFinite ν] (m n : ℕ) :
    gatedStageDefect ν m n ≤ 2 * gatedStageEnergy ν m + 2 * gatedStageEnergy ν n := by
  unfold gatedStageDefect gatedStageEnergy
  have hmeas : AEMeasurable (fun ω : MarkedEnvironment =>
      2 * rootedSpecificEnergyDensity (decode ω.1) (stageField m ω) 0) (ν.prod gridLaw) :=
    ((measurable_rootedSpecificEnergyDensity_stageField m).const_mul 2).aemeasurable
  calc (∫⁻ ω : MarkedEnvironment,
        rootedSpecificEnergyDensity (decode ω.1) (stageDifferenceField m n ω) 0 ∂ν.prod gridLaw)
      ≤ ∫⁻ ω : MarkedEnvironment,
          (2 * rootedSpecificEnergyDensity (decode ω.1) (stageField m ω) 0
            + 2 * rootedSpecificEnergyDensity (decode ω.1) (stageField n ω) 0) ∂ν.prod gridLaw :=
        lintegral_mono fun ω =>
          MarkedStageCoefficientScaling.rootedSpecificEnergyDensity_sub_le (decode ω.1)
            (decode_geometry ω.1) (stageField m ω) (stageField n ω) 0
    _ = 2 * (∫⁻ ω : MarkedEnvironment,
            rootedSpecificEnergyDensity (decode ω.1) (stageField m ω) 0 ∂ν.prod gridLaw)
        + 2 * ∫⁻ ω : MarkedEnvironment,
            rootedSpecificEnergyDensity (decode ω.1) (stageField n ω) 0 ∂ν.prod gridLaw := by
        rw [lintegral_add_left' hmeas,
          lintegral_const_mul' 2 _ (by simp : (2 : ℝ≥0∞) ≠ ∞),
          lintegral_const_mul' 2 _ (by simp : (2 : ℝ≥0∞) ≠ ∞)]

/-- `e_m ≤ 2 e_0 + 2 V_m`, with `V_m = ‖g_0 − g_m‖_*²` the energy of the variation. -/
theorem gatedStageEnergy_le (ν : Measure Env) [SFinite ν] (m : ℕ) :
    gatedStageEnergy ν m ≤ 2 * gatedStageEnergy ν 0 + 2 * gatedStageDefect ν 0 m := by
  unfold gatedStageDefect gatedStageEnergy
  have hmeas : AEMeasurable (fun ω : MarkedEnvironment =>
      2 * rootedSpecificEnergyDensity (decode ω.1) (stageField 0 ω) 0) (ν.prod gridLaw) :=
    ((measurable_rootedSpecificEnergyDensity_stageField 0).const_mul 2).aemeasurable
  calc (∫⁻ ω : MarkedEnvironment,
        rootedSpecificEnergyDensity (decode ω.1) (stageField m ω) 0 ∂ν.prod gridLaw)
      ≤ ∫⁻ ω : MarkedEnvironment,
          (2 * rootedSpecificEnergyDensity (decode ω.1) (stageField 0 ω) 0
            + 2 * rootedSpecificEnergyDensity (decode ω.1) (stageDifferenceField 0 m ω) 0)
            ∂ν.prod gridLaw := by
        refine lintegral_mono fun ω => ?_
        have h := MarkedStageCoefficientScaling.rootedSpecificEnergyDensity_sub_le (decode ω.1)
          (decode_geometry ω.1) (stageField 0 ω) (stageDifferenceField 0 m ω) 0
        rwa [← stageField_eq_sub_var m ω] at h
    _ = 2 * (∫⁻ ω : MarkedEnvironment,
            rootedSpecificEnergyDensity (decode ω.1) (stageField 0 ω) 0 ∂ν.prod gridLaw)
        + 2 * ∫⁻ ω : MarkedEnvironment,
            rootedSpecificEnergyDensity (decode ω.1) (stageDifferenceField 0 m ω) 0
              ∂ν.prod gridLaw := by
        rw [lintegral_add_left' hmeas,
          lintegral_const_mul' 2 _ (by simp : (2 : ℝ≥0∞) ≠ ∞),
          lintegral_const_mul' 2 _ (by simp : (2 : ℝ≥0∞) ≠ ∞)]

/-- **`e_0 < ∞`** for the gated stage energy: `s:lem:e0`. -/
theorem gatedStageEnergy_zero_lt_top (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) : gatedStageEnergy ν 0 < ∞ := by
  rw [gatedStageEnergy_eq ν hν hFE 0]
  exact (MarkedStageCoefficientScaling.markedStageEnergy_zero_ne_top ν hν hFE).lt_top

/-! ### Route (A): the energy of the variation, by two redistributions -/

/-- **The variation energy is the expected owner-block density of `(v_m, v_m)` at any parameter
`k ≥ m`**: the endpoint density of the energy coefficient of `v_m` is `ρ(v_m)` off the
boundary mask, and the redistribution runs from `s:eq:MTP`. -/
theorem gatedStageDefect_zero_eq_ownerBlockDensity (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (m : ℕ) {k : ℕ} (hmk : m ≤ k)
    (hk : k ≠ 0) :
    gatedStageDefect ν 0 m
      = ∫⁻ ω : MarkedEnvironment,
          (posField (varOwnership m hmk hk)).ownerBlockDensity ω ∂(ν.prod gridLaw) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have h1 : gatedStageDefect ν 0 m
      = ∫⁻ ω : MarkedEnvironment,
          (posField (varOwnership m hmk hk)).rootEndpointDensity ω ∂(ν.prod gridLaw) := by
    unfold gatedStageDefect
    refine lintegral_congr_ae ?_
    filter_upwards [ae_bdry ν hν] with ω hω
    exact ((posField_rootEndpointDensity _ ω).trans
      (energyEndpointDensity_eq_rootedSpecificEnergyDensity ω.1 _ hω)).symm
  have h2 : (∫⁻ ω : MarkedEnvironment,
        (posField (varOwnership m hmk hk)).rootEndpointDensity ω ∂(ν.prod gridLaw))
      = ∫⁻ ω : MarkedEnvironment,
          (posField (varOwnership m hmk hk)).ownerBlockDensity ω ∂(ν.prod gridLaw) :=
    lintegral_rootEndpointDensity_eq_ownerBlockDensity_posField
      (similarityTransportedField_stageDifferenceField 0 m) (varOwnership m hmk hk)
      (fun ω q => varOwnership_owner m hmk hk ω q) ν hν (measurable_pairCoeff_var m)
      (ae_exists_originSelected ν hν hFE hkpos)
  exact h1.trans h2

/-- **The block density of the variation is dominated by that of the owned energy field of the
centroid embedding**, at every configuration of the good event with `s:eq:Wbound` and a
selected origin block: the active-edge Pythagoras at `S_m(0)`. -/
theorem ownerBlockDensity_var_le_base (m : ℕ) (hm : m ≠ 0) {ω : MarkedEnvironment}
    (hG : ω.1 ∈ SublinearEvent) (hW : SpatialDiameterCellBounds (decode ω.1))
    (hsel : ∃ k : ℤ, OriginSelected (decode ω.1) ω.2 (m : ℝ) k) :
    (posField (varOwnership m le_rfl hm)).ownerBlockDensity ω
      ≤ (ownedEnergyField actualReRooting (m : ℝ) (stageField 0)).ownerBlockDensity ω := by
  have hv : (posField (varOwnership m le_rfl hm)).ownerBlockDensity ω
      = activeEnergySum (decode ω.1) ω.2 (m : ℝ) (blockSquareIndex (decode ω.1) ω.2 (m : ℝ))
          (fun v => stageDifferenceField 0 m ω v.1)
        / (2 * ENNReal.ofReal (actualReRooting.blockSideAt (m : ℝ) ω ^ 2)) :=
    ownerBlockDensity_eq_activeEnergySum (posField (varOwnership m le_rfl hm))
      (stageDifferenceField 0 m) (fun ω q => varOwnership_owner m le_rfl hm ω q)
      (fun ω p _ _ => varOwnership_weight m le_rfl hm ω p) ω
  have hb : (ownedEnergyField actualReRooting (m : ℝ) (stageField 0)).ownerBlockDensity ω
      = activeEnergySum (decode ω.1) ω.2 (m : ℝ) (blockSquareIndex (decode ω.1) ω.2 (m : ℝ))
          (fun v => stageField 0 ω v.1)
        / (2 * ENNReal.ofReal (actualReRooting.blockSideAt (m : ℝ) ω ^ 2)) :=
    ownerBlockDensity_eq_activeEnergySum (ownedEnergyField actualReRooting (m : ℝ) (stageField 0))
      (stageField 0) (fun ω q => ownedEnergyField_owner actualReRooting (m : ℝ) (stageField 0) ω q)
      (fun ω p s h =>
        ownedEnergyField_weight_of_eq_some actualReRooting (m : ℝ) (stageField 0) ω h) ω
  rw [hv, hb]
  refine ENNReal.div_le_div_right ?_ _
  have hblock : Selected (decode ω.1) ω.2 (m : ℝ) (blockSquareIndex (decode ω.1) ω.2 (m : ℝ)) :=
    originSelected_blockLevel hsel
  have hne : ∃ f, IsBlockInterpolation (decode ω.1) ω.2 m f :=
    exists_isBlockInterpolation_of_spatialCellBounds (decode ω.1) (decode_geometry ω.1) hW ω.2 m
  have hmin : CentroidTraceMinimizer (decode ω.1)
      (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (m : ℝ))) (phi (decode ω.1) ω.2 m) :=
    centroidTraceMinimizer_phi ω.2 hm hne hblock
  have hpin : ∀ v ∈ skeleton (decode ω.1) ω.2 (m : ℝ),
      phi (decode ω.1) ω.2 m v = cellCentroid (decode ω.1) v :=
    fun v hv => phi_eq_cellCentroid_on_own_skeleton (decode ω.1) ω.2 m hv
  have hbE : vectorEnergy (restrictGraph (decode ω.1).graph
      (patchVertices (decode ω.1) (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (m : ℝ)))))
      (fun v => cellCentroid (decode ω.1) v.1) < ∞ :=
    vectorEnergy_cellCentroid_patch_lt_top (decode ω.1) (decode_geometry ω.1) _
      (localDiameterPiMass_patchVertices (decode ω.1)
        (spatialDiameterPiBounds_of_cellBounds (decode ω.1) hW) _)
  have h0 : stageField 0 ω = cellCentroid (decode ω.1) := by
    rw [stageField_eq_phi (m := 0) hG, phi_zero]
  have hm' : stageField m ω = phi (decode ω.1) ω.2 m := stageField_eq_phi hG
  have hvar : (fun v : patchVertices (decode ω.1)
        (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (m : ℝ))) =>
          stageDifferenceField 0 m ω v.1)
      = fun v => cellCentroid (decode ω.1) v.1 - phi (decode ω.1) ω.2 m v.1 := by
    funext v
    show stageField 0 ω v.1 - stageField m ω v.1 = _
    rw [h0, hm']
  have hbase : (fun v : patchVertices (decode ω.1)
        (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (m : ℝ))) => stageField 0 ω v.1)
      = fun v => cellCentroid (decode ω.1) v.1 := by
    funext v
    rw [h0]
  rw [hvar, hbase]
  exact activeEnergySum_sub_le (decode ω.1) ω.2 (m : ℝ) _ hblock hmin hbE hpin

/-- **The expected owner-block density of the owned energy field of the centroid embedding is
at most `e_0`**: redistribution back to the endpoint density, which is dominated by `ρ(b)`. -/
theorem lintegral_ownerBlockDensity_base_le (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) {m : ℕ} (hm : m ≠ 0) :
    (∫⁻ ω : MarkedEnvironment,
        (ownedEnergyField actualReRooting (m : ℝ) (stageField 0)).ownerBlockDensity ω
        ∂(ν.prod gridLaw))
      ≤ gatedStageEnergy ν 0 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have heq : (∫⁻ ω : MarkedEnvironment,
        (ownedEnergyField actualReRooting (m : ℝ) (stageField 0)).rootEndpointDensity ω
        ∂(ν.prod gridLaw))
      = ∫⁻ ω : MarkedEnvironment,
          (ownedEnergyField actualReRooting (m : ℝ) (stageField 0)).ownerBlockDensity ω
          ∂(ν.prod gridLaw) :=
    lintegral_rootEndpointDensity_eq_ownerBlockDensity_ownedEnergyField
      (similarityTransportedField_stageField 0) ν hν measurable_pairCoeff_base
      (ae_exists_originSelected ν hν hFE hmpos)
  rw [← heq]
  unfold gatedStageEnergy
  refine lintegral_mono_ae ?_
  filter_upwards [ae_bdry ν hν] with ω hω
  calc (ownedEnergyField actualReRooting (m : ℝ) (stageField 0)).rootEndpointDensity ω
      ≤ energyEndpointDensity ω.1 (stageField 0 ω) :=
        rootEndpointDensity_ownedEnergyField_le _ _ _ ω
    _ = rootedSpecificEnergyDensity (decode ω.1) (stageField 0 ω) 0 :=
        energyEndpointDensity_eq_rootedSpecificEnergyDensity ω.1 _ hω

/-- **The energy of every variation is finite**: `V_m ≤ e_0 < ∞`. -/
theorem gatedStageDefect_zero_lt_top (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (m : ℕ) :
    gatedStageDefect ν 0 m < ∞ := by
  by_cases hm : m = 0
  · subst hm
    refine lt_of_le_of_lt (gatedStageDefect_le ν 0 0) ?_
    have h0 := gatedStageEnergy_zero_lt_top ν hν hFE
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h0, ENNReal.mul_lt_top (by simp) h0⟩
  · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    calc gatedStageDefect ν 0 m
        = ∫⁻ ω : MarkedEnvironment,
            (posField (varOwnership m le_rfl hm)).ownerBlockDensity ω ∂(ν.prod gridLaw) :=
          gatedStageDefect_zero_eq_ownerBlockDensity ν hν hFE m le_rfl hm
      _ ≤ ∫⁻ ω : MarkedEnvironment,
            (ownedEnergyField actualReRooting (m : ℝ) (stageField 0)).ownerBlockDensity ω
            ∂(ν.prod gridLaw) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_good ν hν hFE, ae_cellBounds ν hν hFE,
            ae_exists_originSelected ν hν hFE hmpos] with ω h1 h2 h3
          exact ownerBlockDensity_var_le_base m hm h1 h2 h3
      _ ≤ gatedStageEnergy ν 0 := lintegral_ownerBlockDensity_base_le ν hν hFE hm
      _ < ∞ := gatedStageEnergy_zero_lt_top ν hν hFE

/-- **Route (A): every stage has finite specific energy, without the projection bound.** -/
theorem gatedStageEnergy_lt_top (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (m : ℕ) :
    gatedStageEnergy ν m < ∞ :=
  lt_of_le_of_lt (gatedStageEnergy_le ν m)
    (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top (by simp) (gatedStageEnergy_zero_lt_top ν hν hFE),
        ENNReal.mul_lt_top (by simp) (gatedStageDefect_zero_lt_top ν hν hFE m)⟩)

/-- Every stage defect is finite. -/
theorem gatedStageDefect_lt_top (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (m n : ℕ) :
    gatedStageDefect ν m n < ∞ :=
  lt_of_le_of_lt (gatedStageDefect_le ν m n)
    (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top (by simp) (gatedStageEnergy_lt_top ν hν hFE m),
        ENNReal.mul_lt_top (by simp) (gatedStageEnergy_lt_top ν hν hFE n)⟩)

/-! ### Route (B): `hmE` -/

/-- **`MarkedStageBlockEnergy ν`, i.e. `hmE`.**  Almost surely the earlier stage field has
finite energy on the patch of the origin block selected at the later parameter. -/
theorem markedStageBlockEnergy (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) : MarkedStageBlockEnergy ν := by
  intro m n hmn
  by_cases hn : n = 0
  · have hm0 : m = 0 := by omega
    subst hm0
    subst hn
    filter_upwards [ae_good ν hν hFE, ae_cellBounds ν hν hFE] with ω hG hW
    have h0 : stageField 0 ω = cellCentroid (decode ω.1) := by
      rw [stageField_eq_phi (m := 0) hG, phi_zero]
    rw [h0]
    exact vectorEnergy_cellCentroid_patch_lt_top (decode ω.1) (decode_geometry ω.1) _
      (localDiameterPiMass_patchVertices (decode ω.1)
        (spatialDiameterPiBounds_of_cellBounds (decode ω.1) hW) _)
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hfin : (∫⁻ ω : MarkedEnvironment,
        (posField (varOwnership m hmn hn)).ownerBlockDensity ω ∂(ν.prod gridLaw)) ≠ ∞ := by
      rw [← gatedStageDefect_zero_eq_ownerBlockDensity ν hν hFE m hmn hn]
      exact (gatedStageDefect_zero_lt_top ν hν hFE m).ne
    have hae : ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw),
        (posField (varOwnership m hmn hn)).ownerBlockDensity ω < ∞ :=
      ae_lt_top' (aemeasurable_ownerBlockDensity _
        (fun q => (measurable_pairCoeff_var m q).ennreal_ofReal)
        (fun q c => measurableSet_labelOwner_eq_some (n : ℝ) q c)
        (ae_existsUnique_originSelected ν hν hFE hnpos)) hfin
    filter_upwards [ae_good ν hν hFE, ae_cellBounds ν hν hFE,
      ae_exists_originSelected ν hν hFE hnpos, hae] with ω hG hW hsel hlt
    have hA : activeEnergySum (decode ω.1) ω.2 (n : ℝ)
        (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))
        (fun v => stageDifferenceField 0 m ω v.1) < ∞ :=
      activeEnergySum_lt_top_of_ownerBlockDensity_lt_top (posField (varOwnership m hmn hn))
        (stageDifferenceField 0 m) (fun ω q => varOwnership_owner m hmn hn ω q)
        (fun ω p _ _ => varOwnership_weight m hmn hn ω p) ω hlt
    have hblock : Selected (decode ω.1) ω.2 (n : ℝ)
        (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)) := originSelected_blockLevel hsel
    have hEu : vectorEnergy (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1) (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
        (fun v => stageDifferenceField 0 m ω v.1) < ∞ :=
      vectorEnergy_lt_top_of_activeEnergySum_lt_top (decode ω.1) ω.2 (n : ℝ) _ hblock
        (fun v hv => var_eq_zero_on_skeleton m hmn hn ω hv) hA
    have hEb : vectorEnergy (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1) (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
        (fun v => stageField 0 ω v.1) < ∞ := by
      have h0 : stageField 0 ω = cellCentroid (decode ω.1) := by
        rw [stageField_eq_phi (m := 0) hG, phi_zero]
      rw [h0]
      exact vectorEnergy_cellCentroid_patch_lt_top (decode ω.1) (decode_geometry ω.1) _
        (localDiameterPiMass_patchVertices (decode ω.1)
          (spatialDiameterPiBounds_of_cellBounds (decode ω.1) hW) _)
    have hsub : (fun v : patchVertices (decode ω.1)
          (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) => stageField m ω v.1)
        = (fun v : patchVertices (decode ω.1)
            (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) => stageField 0 ω v.1)
          - fun v : patchVertices (decode ω.1)
            (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) =>
              stageDifferenceField 0 m ω v.1 := by
      funext v
      show stageField m ω v.1 = stageField 0 ω v.1 - (stageField 0 ω v.1 - stageField m ω v.1)
      rw [sub_sub_cancel]
    rw [hsub]
    exact vectorEnergy_lt_top_of_coord _ fun i =>
      NestedEnergyProjections.hasFiniteEnergy_coord_sub _ hEu hEb i

/-! ### Route (C): the endpoint densities -/

/-- **`MarkedStagePairingEndpointFinite ν`.**  Both endpoint densities of the signed pairing
coefficient are dominated by `ρ(φ_n) + ρ(φ_m − φ_n)`, whose expectation is finite by (A). -/
theorem markedStagePairingEndpointFinite (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    MarkedStagePairingEndpointFinite ν := by
  intro m n _
  have hbound : ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw),
      posEndpointDensity m n ω
          ≤ rootedSpecificEnergyDensity (decode ω.1) (stageField n ω) 0
            + rootedSpecificEnergyDensity (decode ω.1) (stageDifferenceField m n ω) 0 ∧
        negEndpointDensity m n ω
          ≤ rootedSpecificEnergyDensity (decode ω.1) (stageField n ω) 0
            + rootedSpecificEnergyDensity (decode ω.1) (stageDifferenceField m n ω) 0 := by
    filter_upwards [ae_bdry ν hν] with ω hω
    exact ⟨endpointDensity_le_of_le_abs ω.1 (stageField n ω) (stageDifferenceField m n ω) hω
        (fun a k => pairCoeff ω.1 (stageField n ω) (stageDifferenceField m n ω) (a, k))
        (fun a k => le_abs_self _),
      endpointDensity_le_of_le_abs ω.1 (stageField n ω) (stageDifferenceField m n ω) hω
        (fun a k => -(pairCoeff ω.1 (stageField n ω) (stageDifferenceField m n ω) (a, k)))
        (fun a k => neg_le_abs _)⟩
  have hfin : (∫⁻ ω : MarkedEnvironment,
      (rootedSpecificEnergyDensity (decode ω.1) (stageField n ω) 0
        + rootedSpecificEnergyDensity (decode ω.1) (stageDifferenceField m n ω) 0)
      ∂(ν.prod gridLaw)) ≠ ∞ := by
    rw [lintegral_add_left' (measurable_rootedSpecificEnergyDensity_stageField n).aemeasurable]
    exact ENNReal.add_ne_top.2
      ⟨(gatedStageEnergy_lt_top ν hν hFE n).ne, (gatedStageDefect_lt_top ν hν hFE m n).ne⟩
  constructor
  · exact ne_top_of_le_ne_top hfin (lintegral_mono_ae (hbound.mono fun ω h => h.1))
  · exact ne_top_of_le_ne_top hfin (lintegral_mono_ae (hbound.mono fun ω h => h.2))

/-! ### `hproj` and its consumers -/

/-- **`hproj` is a theorem**: `SpecificEnergyConvergence.MarkedNestedProjectionBound ν` from
`s:eq:MTP` and the (FE) moment alone. -/
theorem markedNestedProjectionBound (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    SpecificEnergyConvergence.MarkedNestedProjectionBound ν :=
  markedNestedProjectionBound_of_blockData ν hν hFE (markedStageBlockEnergy ν hν hFE)
    (markedStagePairingEndpointFinite ν hν hFE)

end ReflectedGMS.StageBlockEnergy
