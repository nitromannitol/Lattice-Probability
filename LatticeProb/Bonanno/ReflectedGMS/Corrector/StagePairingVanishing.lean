/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StagePairingVanishing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StagePairingBlockOwnership
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StagePairingProjection
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PairingTransportWeld
import LatticeProb.Bonanno.ReflectedGMS.Corrector.TransportAeGating
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedEnergyProjections
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchCentroidTraceFiniteEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolantSelectionCandidate
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodMarkedSpace

/-!
# `MarkedStagePairingVanishes` from two block-local inputs

`Corrector/StagePairingProjection` reduces `hproj` (and hence `hspec`) to the single input
`MarkedStagePairingVanishes ν`.  This module reduces *that* to two block-local statements at
the selected origin block, on the actual marked space `Env × Grid` — **no re-instantiation of
the transport chain on a good subtype is needed**.

## Why the good subtype is not needed

`Corrector/PairingTransportWeld` is stated for
`PairingOwnershipInstance.activePairingOwnership`, whose construction demands
`SelectionCoversOn` at **every** configuration; that is false at a general `ω`.  But the stage
fields are already gated: `HarmonicCoordinateAssembly.gatedApproximant` is `0` off
`SublinearEvent`, so `MarkedStageFieldCovariance.stageDifferenceField m n ω` vanishes
identically there, and `StagePairingBlockOwnership.gatedPairingOwnership` builds the ownership
datum from the weaker *cover-or-vanish* hypothesis.  On `SublinearEvent` itself
`StagePairingSkeletonData.selectionCoversOn_of_mem_sublinearEvent` supplies the cover.  So the
whole weld runs on `Env × Grid` with `ActualMarkedBlockTransport.actualReRooting`, and the
covariance producers of `Corrector/OwnedFieldLabelTransport` apply verbatim.

## What is discharged

* **`hmeas`** — `BlockInterpolantSelectionCandidate.measurable_gatedApproximant`, unconditional.
* **`hcoeff`/`howner`** — `StagePairingBlockOwnership.measurable_pairCoeff_of_labels` and
  `StagePairingBlockOwnership.measurableSet_labelOwner_eq_some`.
* **`hcover`/`hH`** (the two structural data) — pathwise at **every** `ω`, with *no*
  solvability hypothesis: where the per-square Dirichlet problem is unsolvable
  `DyadicApproximation.phi` is *defined* to be the centroid embedding, so the nested pinning
  `s:eq:pinnested` holds in that case too (`phi_eq_cellCentroid_of_not_exists`,
  `stageDifferenceField_eq_zero_on_skeleton'`).  This removes the block-interpolant existence
  input that `Corrector/StagePairingSkeletonData` had to carry.
* **`hsel`** — almost surely, from `Spatial/GoodMarkedSpace.originChainRegular_goodMarked`.
* **`hbdry`** — `PairingOwnershipInstance.ae_notMem_boundaryMask_env`.
* **`hmin`/`hΨE`/`horth`** — almost surely: `s:eq:Wbound`
  (`SpatialMaximalForFiniteEnergy.ae_spatialDiameterCellBounds`, a theorem from `s:eq:MTP` and
  the (FE) moment) makes `phi` the genuine block interpolant, whose
  `DyadicApproximation.CentroidTraceMinimizer` clause carries both the block-local energy of
  the *later* stage and, through
  `NestedEnergyProjections.vectorPairing_sub_eq_zero_of_centroidTraceMinimizer`, the block
  orthogonality.
* **`hmtp`/`hmtm`** — `PairingTransportWeld.markedMassTransport_endpointSpreadTransport` with
  `OwnedFieldLabelTransport.similarityCovariantField_posField`/`negField`.

## What remains open — exactly two statements

* `MarkedStageBlockEnergy ν` (**`hmE`**): almost surely the *earlier* stage field has finite
  energy on the patch graph of the origin block selected at the *later* parameter.  It is the
  hypothesis that `NestedEnergyProjections.blockPythagoras_nested` also carries and calls an
  "explicit geometric hypothesis"; no producer exists anywhere in the tree.  It is **not**
  implied by minimality: `phi n` minimizes on that block, and `phi m` is only an admissible
  competitor, so minimality bounds the wrong side.
* `MarkedStagePairingEndpointFinite ν` (**`hpfin`/`hmfin`**): the two expected endpoint
  densities of the positive and negative parts of the signed coefficient are finite.  This is
  *stronger* than the `Integrable` clause of `MarkedStagePairingVanishes` (that clause is a
  consequence, and is produced here), because the endpoint density sums absolute values edge by
  edge.

Both are stated on `decode e` data, carry no `Summable` and no `HasFiniteEnergy`, and hold
trivially at `m = n` (where the variation vanishes identically).

**This file proves no main theorem** and certifies neither of its two remaining inputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.StagePairingVanishing

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedStageFieldCovariance MarkedBlockAveraging DiameterBlockIndex
open SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open OwnedFieldPairingTransport PairingOwnershipInstance NestedProjectionProducers
open ActualMarkedBlockTransport OwnedFieldLabelTransport StagePairingBlockOwnership
open StagePairingSkeletonData PatchCentroidTraceFiniteEnergy

/-! ### The gate: the stage fields vanish off the good event -/

/-- Off `SublinearEvent` the gated stage difference field vanishes identically. -/
theorem stageDifferenceField_eq_zero_of_notMem (m n : ℕ) {ω : MarkedEnvironment}
    (hG : ω.1 ∉ SublinearEvent) (v : Vertex ω.1.val) :
    stageDifferenceField m n ω v = 0 := by
  show gatedApproximant m ω v.val - gatedApproximant n ω v.val = 0
  rw [gatedApproximant_of_notMem m hG, gatedApproximant_of_notMem n hG, sub_self]

/-- Where the per-square Dirichlet problem has no solution, the canonical block interpolant is
*defined* to be the centroid embedding. -/
theorem phi_eq_cellCentroid_of_not_exists {V : Type*} (F : IndexedCells V) (D : Grid) (k : ℕ)
    (h : ¬ ∃ f : V → Plane, IsBlockInterpolation F D k f) : phi F D k = cellCentroid F := by
  classical
  unfold phi
  rw [dif_neg h]

/-- **The block interpolant is pinned to the centroid on its own skeleton, unconditionally.**
For `k = 0` it *is* the centroid embedding; where the Dirichlet problem is unsolvable it is
again the centroid embedding; otherwise this is the pinning clause of `IsBlockInterpolation`. -/
theorem phi_eq_cellCentroid_on_own_skeleton {V : Type*} [Countable V] (F : IndexedCells V)
    (D : Grid) (k : ℕ) {v : V} (hv : v ∈ skeleton F D (k : ℝ)) :
    phi F D k v = cellCentroid F v := by
  classical
  by_cases h0 : k = 0
  · rw [h0, phi_zero]
  · by_cases hex : ∃ f : V → Plane, IsBlockInterpolation F D k f
    · have hspec := phi_spec_of_exists F D k hex
      rw [IsBlockInterpolation, if_neg h0] at hspec
      exact hspec.1 v hv
    · rw [phi_eq_cellCentroid_of_not_exists F D k hex]

/-- **`hH` for the nested pair, at every configuration and with no solvability hypothesis.**
The gated stage difference field vanishes on the skeleton of the later stage.

Compared with `StagePairingSkeletonData.stageDifferenceField_eq_zero_on_skeleton` this carries
neither `∃ f, IsBlockInterpolation … m f` nor its analogue at `n`: where either is unavailable
`phi` is the centroid embedding, and the identity holds for that reason instead. -/
theorem stageDifferenceField_eq_zero_on_skeleton' {m n : ℕ} (hmn : m ≤ n) (hn : n ≠ 0)
    (ω : MarkedEnvironment) {v : Vertex ω.1.val}
    (hv : v ∈ skeleton (decode ω.1) ω.2 (n : ℝ)) :
    stageDifferenceField m n ω v = 0 := by
  classical
  by_cases hG : ω.1 ∈ SublinearEvent
  · have hn' : phi (decode ω.1) ω.2 n v = cellCentroid (decode ω.1) v :=
      phi_eq_cellCentroid_on_own_skeleton (decode ω.1) ω.2 n hv
    have hm' : phi (decode ω.1) ω.2 m v = cellCentroid (decode ω.1) v := by
      by_cases h0 : m = 0
      · rw [h0, phi_zero]
      · have hsub : v ∈ skeleton (decode ω.1) ω.2 (m : ℝ) :=
          skeleton_subset_skeleton_of_le (decode ω.1) ω.2
            (by exact_mod_cast hmn : ((m : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ))
            (selectionCoversOn_of_mem_sublinearEvent hG ω.2
              (by exact_mod_cast Nat.pos_of_ne_zero h0 : (0 : ℝ) < (m : ℝ))) hv
        exact phi_eq_cellCentroid_on_own_skeleton (decode ω.1) ω.2 m hsub
    show stageField m ω v - stageField n ω v = 0
    rw [stageField_eq_phi (m := m) hG, stageField_eq_phi (m := n) hG, hm', hn', sub_self]
  · exact stageDifferenceField_eq_zero_of_notMem m n hG v

/-- **`hcover` in cover-or-vanish form.**  Where the closed selected squares fail to cover the
plane the environment is off `SublinearEvent`, and the gated variation vanishes there. -/
theorem cover_or_vanish {n : ℕ} (m : ℕ) (hn : n ≠ 0) (ω : MarkedEnvironment)
    (hcov : ¬ SelectionCoversOn (decode ω.1) ω.2 (n : ℝ)) (v : Vertex ω.1.val) :
    stageDifferenceField m n ω v = 0 := by
  by_cases hG : ω.1 ∈ SublinearEvent
  · exact absurd (selectionCoversOn_of_mem_sublinearEvent hG ω.2
      (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < (n : ℝ))) hcov
  · exact stageDifferenceField_eq_zero_of_notMem m n hG v

/-! ### The ownership datum of the nested stage pair -/

/-- The ownership datum of the signed pairing coefficient of the nested stage pair, on the
actual marked space. -/
noncomputable def stageOwnership (m : ℕ) {n : ℕ} (hmn : m ≤ n) (hn : n ≠ 0) :
    PairingOwnership actualReRooting (n : ℝ) (stageField n) (stageDifferenceField m n) :=
  gatedPairingOwnership actualReRooting (n : ℝ) (stageField n) (stageDifferenceField m n)
    (fun ω hcov v => cover_or_vanish m hn ω hcov v)
    (fun ω v hv => stageDifferenceField_eq_zero_on_skeleton' hmn hn ω hv)

/-! ### The two endpoint densities, written without the ownership datum -/

/-- The expected endpoint density of the **positive** part of the signed coefficient. -/
noncomputable def posEndpointDensity (m n : ℕ) (ω : MarkedEnvironment) : ℝ≥0∞ :=
  (originLabel ω.1).elim 0 fun a =>
    (∑' k : ℕ, ENNReal.ofReal
        (pairCoeff ω.1 (stageField n ω) (stageDifferenceField m n ω) (a, k)))
      / (2 * volume (labelCell ω.1 a))

/-- The expected endpoint density of the **negative** part of the signed coefficient. -/
noncomputable def negEndpointDensity (m n : ℕ) (ω : MarkedEnvironment) : ℝ≥0∞ :=
  (originLabel ω.1).elim 0 fun a =>
    (∑' k : ℕ, ENNReal.ofReal
        (-(pairCoeff ω.1 (stageField n ω) (stageDifferenceField m n ω) (a, k))))
      / (2 * volume (labelCell ω.1 a))

theorem rootEndpointDensity_posField (m : ℕ) {n : ℕ} (hmn : m ≤ n) (hn : n ≠ 0) :
    (posField (stageOwnership m hmn hn)).rootEndpointDensity = posEndpointDensity m n := rfl

theorem rootEndpointDensity_negField (m : ℕ) {n : ℕ} (hmn : m ≤ n) (hn : n ≠ 0) :
    (negField (stageOwnership m hmn hn)).rootEndpointDensity = negEndpointDensity m n := rfl

/-! ### The two remaining inputs -/

/-- **`hmE`.**  Almost surely the *earlier* stage field has finite energy on the patch graph of
the origin block selected at the *later* parameter.  No producer exists in the project; see the
module docstring. -/
def MarkedStageBlockEnergy (ν : Measure Env) : Prop :=
  ∀ m n : ℕ, m ≤ n → ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw),
    vectorEnergy (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1)
          (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
      (fun v => stageField m ω v.1) < ∞

/-- **`hpfin`/`hmfin`.**  The two expected endpoint densities of the signed coefficient are
finite. -/
def MarkedStagePairingEndpointFinite (ν : Measure Env) : Prop :=
  ∀ m n : ℕ, m ≤ n →
    (∫⁻ ω : MarkedEnvironment, posEndpointDensity m n ω ∂(ν.prod gridLaw)) ≠ ∞ ∧
      (∫⁻ ω : MarkedEnvironment, negEndpointDensity m n ω ∂(ν.prod gridLaw)) ≠ ∞

/-! ### The almost-sure block data -/

/-- **`hsel` almost surely**: the selected origin block exists at every positive parameter, on
the good set. -/
theorem ae_exists_originSelected (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw),
      ∃ k : ℤ, OriginSelected (decode ω.1) ω.2 r k := by
  have hgood : ∀ᵐ e ∂ν, e ∈ GoodMarkedSpace.goodSet :=
    GoodMarkedSpace.ae_mem_goodSet ν hν hFE.ne
  have hcov : ∀ᵐ e ∂ν, (0 : Plane) ∉ uncoveredSet (decode e) :=
    ReflectedGMS.ae_zero_notMem_uncoveredSet ν hν
  filter_upwards [ae_marked_of_ae_env ν hgood, ae_marked_of_ae_env ν hcov] with ω hω hωcov
  exact GoodMarkedSpace.originChainRegularOn_goodMarked.exists_originSelected'
    (ω := ((⟨ω.1, hω⟩ : GoodMarkedSpace.goodSet), ω.2)) hωcov hr

/-- **The block data at a configuration with `s:eq:Wbound` and a selected origin block.**  The
later stage field has finite block-local energy, the variation has finite block-local energy,
and the two are energy-orthogonal on the block. -/
theorem block_data {m n : ℕ} (hmn : m ≤ n) (hn : n ≠ 0) {ω : MarkedEnvironment}
    (hG : ω.1 ∈ SublinearEvent) (hW : SpatialDiameterCellBounds (decode ω.1))
    (hsel : ∃ k : ℤ, OriginSelected (decode ω.1) ω.2 (n : ℝ) k)
    (hmE : vectorEnergy (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1)
          (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
      (fun v => stageField m ω v.1) < ∞) :
    (vectorEnergy (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1)
          (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
      (fun v => stageField n ω v.1) < ∞) ∧
    (vectorEnergy (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1)
          (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
      (fun v => stageDifferenceField m n ω v.1) < ∞) ∧
    vectorPairing (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1)
          (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
      (fun v => stageField n ω v.1) (fun v => stageDifferenceField m n ω v.1) = 0 := by
  have hblock : Selected (decode ω.1) ω.2 (n : ℝ)
      (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)) := originSelected_blockLevel hsel
  have hne : ∃ f, IsBlockInterpolation (decode ω.1) ω.2 n f :=
    exists_isBlockInterpolation_of_spatialCellBounds (decode ω.1) (decode_geometry ω.1) hW ω.2 n
  have hmin : CentroidTraceMinimizer (decode ω.1)
      (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) (phi (decode ω.1) ω.2 n) :=
    centroidTraceMinimizer_phi ω.2 hn hne hblock
  have hfield : stageField n ω = phi (decode ω.1) ω.2 n := stageField_eq_phi hG
  have hΨE : vectorEnergy (restrictGraph (decode ω.1).graph
      (patchVertices (decode ω.1)
        (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
      (fun v => stageField n ω v.1) < ∞ := by
    rw [hfield]
    exact hmin.1
  have hHE : vectorEnergy (restrictGraph (decode ω.1).graph
      (patchVertices (decode ω.1)
        (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
      (fun v => stageDifferenceField m n ω v.1) < ∞ := by
    have hadd : vectorEnergy (restrictGraph (decode ω.1).graph
        (patchVertices (decode ω.1)
          (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))))
        (fun v => stageField n ω v.1 + stageDifferenceField m n ω v.1) < ∞ := by
      have hfun : (fun v : patchVertices (decode ω.1)
            (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) =>
              stageField n ω v.1 + stageDifferenceField m n ω v.1)
          = fun v => stageField m ω v.1 := by
        funext v
        show stageField n ω v.1 + (stageField m ω v.1 - stageField n ω v.1)
          = stageField m ω v.1
        abel
      rw [hfun]
      exact hmE
    exact vectorEnergy_variation_lt_top actualReRooting (n : ℝ) (stageField n)
      (stageDifferenceField m n) ω hΨE hadd
  refine ⟨hΨE, hHE, ?_⟩
  have hgtr : ∀ v : patchVertices (decode ω.1)
      (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))),
      v.1 ∈ boundaryVertices (decode ω.1)
        (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) →
      stageField m ω v.1 = cellCentroid (decode ω.1) v.1 := by
    intro v hv
    have hskel := mem_skeleton_of_mem_boundaryVertices (decode ω.1) ω.2 (n : ℝ) hblock hv
    have hpin : stageDifferenceField m n ω v.1 = 0 :=
      stageDifferenceField_eq_zero_on_skeleton' hmn hn ω hskel
    have hn' : phi (decode ω.1) ω.2 n v.1 = cellCentroid (decode ω.1) v.1 :=
      phi_eq_cellCentroid_on_own_skeleton (decode ω.1) ω.2 n hskel
    have hval : stageField m ω v.1 - stageField n ω v.1 = 0 := hpin
    have hnf : stageField n ω v.1 = cellCentroid (decode ω.1) v.1 := by
      rw [hfield]; exact hn'
    rw [← hnf]
    have hshift := congrArg (fun x : Plane => x + stageField n ω v.1) hval
    simpa using hshift
  have horth0 := NestedEnergyProjections.vectorPairing_sub_eq_zero_of_centroidTraceMinimizer
    (F := decode ω.1) (Q := square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ)))
    hmin (fun v => stageField m ω v.1) hmE hgtr
  have hdiff : ((fun v : patchVertices (decode ω.1)
        (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) => stageField m ω v.1)
      - fun v : patchVertices (decode ω.1)
        (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) =>
          phi (decode ω.1) ω.2 n v.1)
      = fun v : patchVertices (decode ω.1)
        (square ω.2 (blockSquareIndex (decode ω.1) ω.2 (n : ℝ))) =>
          stageDifferenceField m n ω v.1 := by
    funext v
    show stageField m ω v.1 - phi (decode ω.1) ω.2 n v.1
      = stageField m ω v.1 - stageField n ω v.1
    rw [hfield]
  rw [hfield, ← hdiff]
  exact horth0

/-! ### The weld -/

/-- **The expected rooted pairing density of the nested stage pair vanishes**, for `m ≤ n` with
`n ≠ 0`, from the manuscript's own environment hypotheses and the two block-local inputs. -/
theorem integral_rootedPairingDensity_stage_eq_zero (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hblk : MarkedStageBlockEnergy ν) (hend : MarkedStagePairingEndpointFinite ν)
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≠ 0) :
    Integrable (fun ω : MarkedEnvironment =>
        SpecificEnergyPolarization.rootedPairingDensity (decode ω.1) (stageField n ω)
          (stageDifferenceField m n ω) 0) (ν.prod gridLaw)
      ∧ (∫ ω : MarkedEnvironment,
          SpecificEnergyPolarization.rootedPairingDensity (decode ω.1) (stageField n ω)
            (stageDifferenceField m n ω) 0 ∂(ν.prod gridLaw)) = 0 := by
  classical
  have hO : ∀ (ω : MarkedEnvironment) (q : ℕ × ℕ),
      (stageOwnership m hmn hn).owner ω q = labelOwner actualReRooting (n : ℝ) ω q :=
    fun _ _ => rfl
  -- measurability of the signed coefficient
  have hcoeff : ∀ q : ℕ × ℕ, Measurable fun ω : MarkedEnvironment =>
      pairCoeff ω.1 (stageField n ω) (stageDifferenceField m n ω) q := by
    intro q
    have hLΨ : ∀ k : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant n ω k :=
      fun k => BlockInterpolantSelectionCandidate.measurable_gatedApproximant n k
    have hLH : ∀ k : ℕ, Measurable fun ω : MarkedEnvironment =>
        gatedApproximant m ω k - gatedApproximant n ω k := fun k =>
      (BlockInterpolantSelectionCandidate.measurable_gatedApproximant m k).sub
        (BlockInterpolantSelectionCandidate.measurable_gatedApproximant n k)
    exact measurable_pairCoeff_of_labels (E := fun ω : MarkedEnvironment => ω.1)
      measurable_fst hLΨ hLH q
  have howner : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {ω : MarkedEnvironment | labelOwner actualReRooting (n : ℝ) ω q = some c} :=
    fun q c => measurableSet_labelOwner_eq_some (n : ℝ) q c
  have hwp : ∀ q : ℕ × ℕ, Measurable fun ω : MarkedEnvironment =>
      (posField (stageOwnership m hmn hn)).weight ω q := fun q => (hcoeff q).ennreal_ofReal
  have hwm : ∀ q : ℕ × ℕ, Measurable fun ω : MarkedEnvironment =>
      (negField (stageOwnership m hmn hn)).weight ω q := fun q => (hcoeff q).neg.ennreal_ofReal
  have how : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {ω : MarkedEnvironment |
        (posField (stageOwnership m hmn hn)).owner ω q = some c} := howner
  have how' : ∀ (q : ℕ × ℕ) (c : SquareIndex),
      MeasurableSet {ω : MarkedEnvironment |
        (negField (stageOwnership m hmn hn)).owner ω q = some c} := howner
  -- the two single-kernel mass-transport identities
  have hmtp := PairingTransportWeld.markedMassTransport_endpointSpreadTransport
    (posField (stageOwnership m hmn hn)) ν hν hwp how
    (similarityCovariantField_posField (stageOwnership m hmn hn) hO
      (similarityTransportedField_stageField n)
      (similarityTransportedField_stageDifferenceField m n))
  have hmtm := PairingTransportWeld.markedMassTransport_endpointSpreadTransport
    (negField (stageOwnership m hmn hn)) ν hν hwm how'
    (similarityCovariantField_negField (stageOwnership m hmn hn) hO
      (similarityTransportedField_stageField n)
      (similarityTransportedField_stageDifferenceField m n))
  -- almost-sure structural data
  have hsel : ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw),
      ∃ k : ℤ, OriginSelected (decode ω.1) ω.2 (n : ℝ) k :=
    ae_exists_originSelected ν hν hFE
      (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < (n : ℝ))
  have hbdry : ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw),
      (0 : Plane) ∉ RootDensities.boundaryMask (decode ω.1) :=
    ae_notMem_boundaryMask_env actualReRooting
      (PairingTransportWeld.massTransport_map_env_prod ν hν) measurable_fst
  have hWae : ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw),
      SpatialDiameterCellBounds (decode ω.1) :=
    ae_marked_of_ae_env ν (SpatialMaximalForFiniteEnergy.ae_spatialDiameterCellBounds ν hν hFE.ne)
  have hGae : ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw), ω.1 ∈ SublinearEvent :=
    ae_marked_of_ae_env ν (ae_mem_sublinearEvent ν hν hFE.ne)
  -- the block data
  have hsum : ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw), Summable fun q : ℕ × ℕ =>
      ((posField (stageOwnership m hmn hn)).ownedByOriginBlock ω).indicator
        (pairCoeff ω.1 (stageField n ω) (stageDifferenceField m n ω)) q := by
    filter_upwards [hsel, hWae, hGae, hblk m n hmn] with ω h1 h2 h3 h4
    obtain ⟨hΨE, hHE, -⟩ := block_data hmn hn h3 h2 h1 h4
    exact summable_indicator_ownedByOriginBlock_of_energies (stageOwnership m hmn hn) hO
      (fun ω' v hv => stageDifferenceField_eq_zero_on_skeleton' hmn hn ω' hv) ω h1 hΨE hHE
  have hzero : ∀ᵐ ω : MarkedEnvironment ∂(ν.prod gridLaw), (∑' q : ℕ × ℕ,
      ((posField (stageOwnership m hmn hn)).ownedByOriginBlock ω).indicator
        (pairCoeff ω.1 (stageField n ω) (stageDifferenceField m n ω)) q) = 0 := by
    filter_upwards [hsel, hWae, hGae, hblk m n hmn] with ω h1 h2 h3 h4
    obtain ⟨hΨE, hHE, horth⟩ := block_data hmn hn h3 h2 h1 h4
    exact tsum_indicator_ownedByOriginBlock_eq_zero_of_orthogonality (stageOwnership m hmn hn) hO
      (fun ω' v hv => stageDifferenceField_eq_zero_on_skeleton' hmn hn ω' hv) ω h1 hΨE hHE horth
  -- the two endpoint finiteness inputs
  obtain ⟨hpfin, hmfin⟩ := hend m n hmn
  have hpfin' : (∫⁻ ω : MarkedEnvironment,
      (posField (stageOwnership m hmn hn)).rootEndpointDensity ω ∂(ν.prod gridLaw)) ≠ ∞ := by
    rw [rootEndpointDensity_posField m hmn hn]; exact hpfin
  have hmfin' : (∫⁻ ω : MarkedEnvironment,
      (negField (stageOwnership m hmn hn)).rootEndpointDensity ω ∂(ν.prod gridLaw)) ≠ ∞ := by
    rw [rootEndpointDensity_negField m hmn hn]; exact hmfin
  refine ⟨?_, TransportAeGating.integral_rootedPairingDensity_eq_zero_ae
    (stageOwnership m hmn hn) hmtp hmtm measurable_fst hcoeff hsel hpfin' hmfin' hsum hzero
    hbdry⟩
  -- the integrability clause
  have hpmeas : Measurable (posField (stageOwnership m hmn hn)).rootEndpointDensity :=
    MeasurableEndpointTransport.measurable_rootEndpointDensity _ measurable_fst hwp
  have hmmeas : Measurable (negField (stageOwnership m hmn hn)).rootEndpointDensity :=
    MeasurableEndpointTransport.measurable_rootEndpointDensity _ measurable_fst hwm
  have hIp : Integrable (fun ω : MarkedEnvironment =>
      ((posField (stageOwnership m hmn hn)).rootEndpointDensity ω).toReal) (ν.prod gridLaw) :=
    integrable_toReal_of_lintegral_ne_top hpmeas.aemeasurable hpfin'
  have hIm : Integrable (fun ω : MarkedEnvironment =>
      ((negField (stageOwnership m hmn hn)).rootEndpointDensity ω).toReal) (ν.prod gridLaw) :=
    integrable_toReal_of_lintegral_ne_top hmmeas.aemeasurable hmfin'
  refine (hIp.sub hIm).congr ?_
  filter_upwards [hbdry] with ω hω
  exact toReal_rootEndpointDensity_sub_eq_rootedPairingDensity (stageOwnership m hmn hn) ω hω

/-! ### `MarkedStagePairingVanishes`, and the two consumers -/

/-- **`MarkedStagePairingVanishes` from the two block-local inputs.**  The diagonal case
`m = n` is a theorem (`StagePairingProjection.rootedPairingDensity_stageDifferenceField_self`),
and it covers `n = 0` because `m ≤ n` forces `m = n = 0` there. -/
theorem markedStagePairingVanishes_of_blockData (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hblk : MarkedStageBlockEnergy ν) (hend : MarkedStagePairingEndpointFinite ν) :
    StagePairingProjection.MarkedStagePairingVanishes ν := by
  intro m n hmn
  by_cases hn : n = 0
  · have hm0 : m = 0 := by omega
    subst hm0
    subst hn
    have hzero : (fun ω : MarkedEnvironment =>
        SpecificEnergyPolarization.rootedPairingDensity (decode ω.1) (stageField 0 ω)
          (stageDifferenceField 0 0 ω) 0) = fun _ : MarkedEnvironment => (0 : ℝ) :=
      funext fun ω =>
        StagePairingProjection.rootedPairingDensity_stageDifferenceField_self 0 ω
    constructor
    · rw [hzero]
      exact integrable_zero _ _ _
    · rw [hzero]
      exact integral_zero _ _
  · exact integral_rootedPairingDensity_stage_eq_zero ν hν hFE hblk hend hmn hn

/-- **`hproj` from the two block-local inputs**, with `hmeas` discharged unconditionally. -/
theorem markedNestedProjectionBound_of_blockData (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hblk : MarkedStageBlockEnergy ν) (hend : MarkedStagePairingEndpointFinite ν) :
    SpecificEnergyConvergence.MarkedNestedProjectionBound ν :=
  StagePairingProjection.markedNestedProjectionBound_of_stagePairing ν hν hFE
    (fun k j => BlockInterpolantSelectionCandidate.measurable_gatedApproximant k j)
    (markedStagePairingVanishes_of_blockData ν hν hFE hblk hend)

end ReflectedGMS.StagePairingVanishing
