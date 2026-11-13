/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.CopyDifferenceCrossPairing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GridCrossOrthogonalityOwnership
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GridCrossOrthogonalityPolarization
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRectangleOrthogonalityProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedStageCoefficientScaling
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedDensityMeasurabilityProducer
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolantSelectionGate
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SimilarityCentroidCovariance
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GoodMarkedScaleAction

/-!
# The stagewise cross identities `⟪Φ, φ_m − b⟫_* = 0` on the coupled two-grid space

This is the first half of the manuscript's proof of `s:prop:gridindependence` (tex:583):

> *By Proposition `s:prop:limit`, `Φ¹` satisfies full variational orthogonality on every block of
> the second grid.  The variation `φ_m² − b` vanishes on that partition's boundary cells.  Signed
> redistribution therefore gives `⟪g¹, g_m² − g₀⟫ = 0`.*

On the coupled space `CoupledSpace = Env × Grid × Grid` with block grid the **first** copy
`p.2.1`, the two fields are

* `crossPotential ms p = markedPotential ms (p.1, p.2.2)` — the limiting potential of the
  **other** grid (the manuscript's `Φ¹` when the blocks come from `𝔻₂`), and
  `blockPotential ms p = markedPotential ms (p.1, p.2.1)` — the limiting potential of the block
  grid itself (the manuscript's *"also `⟪g¹, g¹ − g₀⟫ = 0` by the same argument with the first
  grid"*);
* `gatedVariation m p = 1_{p.1 ∈ goodSet} (φ_m^{p.2.1} − b)` — the stage-`m` variation of the
  block grid, gated by the good set so that it vanishes on the skeleton **pathwise** (on the
  good set `φ_m` is either a block interpolant, hence pinned to `b` on the skeleton, or the
  centroid field itself) and vanishes identically wherever the selected squares might fail to
  cover the plane (they do cover it on the good set,
  `GridCrossOrthogonalityOwnership.selectionCoversOn_of_mem_goodSet`).

`integral_pairing_gatedVariation_eq_zero` is the identity for any coupled transported field
`Ψ` which is almost surely `FullRectangleOrthogonality` and has finite expected specific energy;
`integral_crossPairing_eq_zero` and `integral_blockPairing_eq_zero` are its two instances.  The
inputs beyond the manuscript's `s:eq:MTP` and (FE) moment are `hmeas` (now a theorem elsewhere),
`hproj` (`MarkedNestedProjectionBound`, for the finiteness of the stage energies), `hconv` and
`hpatch` (both produced from `hproj` and `hmeas` in the five-input assembly; `hpatch` is what
makes the limiting potential fully orthogonal on every rectangle).

**This file proves no main theorem.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace ReflectedGMS.CopyDifferenceCrossPairing

open Code StatementIngredients EnvironmentLaws RootDensities DyadicApproximation
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedBlockAveraging SpecificEnergyRedistribution SpecificEnergyRedistribution.OwnedEdgeField
open DyadicGridLaw GridIndependenceCoupling CopyDifferenceDensitySimilarity
open NestedProjectionProducers PairingOwnershipInstance OwnedFieldPairingTransport
open SpecificEnergyDensitySimilarity SpecificEnergyPolarization
open GridCrossOrthogonalityTransport GridCrossOrthogonalityOwnership
open GridCrossOrthogonalityPolarization GoodMarkedSpace GoodEnvironmentSet
open PatchCentroidTraceFiniteEnergy MarkedDensityMeasurabilityProducer

/-! ### The fields -/

/-- The limiting potential of the passive (second) grid, as a coupled field. -/
noncomputable def crossPotential (ms : ℕ → ℕ) (p : CoupledSpace) : Vertex p.1.val → Plane :=
  markedPotential ms (p.1, p.2.2)

/-- The limiting potential of the block (first) grid, as a coupled field. -/
noncomputable def blockPotential (ms : ℕ → ℕ) (p : CoupledSpace) : Vertex p.1.val → Plane :=
  markedPotential ms (p.1, p.2.1)

/-- **The gated stage variation** `1_{good}(φ_m − b)` of the block grid. -/
noncomputable def gatedVariation (m : ℕ) (p : CoupledSpace) : Vertex p.1.val → Plane :=
  fun v => if p.1 ∈ goodSet then
    MarkedStageFieldCovariance.stageField m (p.1, p.2.1) v - cellCentroid (decode p.1) v
  else 0

theorem gatedVariation_of_mem (m : ℕ) {p : CoupledSpace} (hg : p.1 ∈ goodSet)
    (v : Vertex p.1.val) :
    gatedVariation m p v
      = MarkedStageFieldCovariance.stageField m (p.1, p.2.1) v - cellCentroid (decode p.1) v := by
  unfold gatedVariation
  rw [if_pos hg]

theorem gatedVariation_of_notMem (m : ℕ) {p : CoupledSpace} (hg : p.1 ∉ goodSet)
    (v : Vertex p.1.val) : gatedVariation m p v = 0 := by
  unfold gatedVariation
  rw [if_neg hg]

/-- On the good set the gated variation is the concrete `φ_m − b`. -/
theorem gatedVariation_eq_phi_sub (m : ℕ) {p : CoupledSpace} (hg : p.1 ∈ goodSet) :
    gatedVariation m p = fun v => phi (decode p.1) p.2.1 m v - cellCentroid (decode p.1) v := by
  funext v
  rw [gatedVariation_of_mem m hg v,
    MarkedStageFieldCovariance.stageField_eq_phi (m := m) (p := (p.1, p.2.1))
      (mem_sublinearEvent_of_mem_goodSet hg)]

/-! ### Transport -/

theorem coupledTransportedField_crossPotential (ms : ℕ → ℕ) :
    CoupledTransportedField (crossPotential ms) :=
  coupledTransportedField_markedPotential_snd ms

theorem coupledTransportedField_blockPotential (ms : ℕ → ℕ) :
    CoupledTransportedField (blockPotential ms) :=
  coupledTransportedField_markedPotential_fst ms

/-- The good set is invariant under the joint similarity. -/
theorem mem_goodSet_iff_coupledSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (p : CoupledSpace) :
    p.1 ∈ goodSet ↔ (coupledSimilarity s u hs p).1 ∈ goodSet :=
  ⟨fun hg => goodEnvironment_similarityTargetEnv s u hs hg,
    fun hg => GoodMarkedScaleAction.mem_goodSet_of_similarityTargetEnv_mem hs u hg⟩

/-- **The gated variation transports along every joint similarity.** -/
theorem coupledTransportedField_gatedVariation (m : ℕ) :
    CoupledTransportedField (gatedVariation m) := by
  intro s u hs p rel h
  by_cases hg : p.1 ∈ goodSet
  · have hg' : (coupledSimilarity s u hs p).1 ∈ goodSet :=
      (mem_goodSet_iff_coupledSimilarity s u hs p).1 hg
    have h1 := coupledTransportedField_stageField_fst m s u hs p rel h
    have h2 : GradientTransported s rel (fun v => cellCentroid (decode p.1) v)
        (fun v => cellCentroid (decode (coupledSimilarity s u hs p).1) v) := by
      intro v w
      show cellCentroid (decode (coupledSimilarity s u hs p).1) (rel w)
          - cellCentroid (decode (coupledSimilarity s u hs p).1) (rel v)
        = s • (cellCentroid (decode p.1) w - cellCentroid (decode p.1) v)
      rw [SimilarityCentroidCovariance.cellCentroid_similarityRelabel h (decode_geometry p.1) w,
        SimilarityCentroidCovariance.cellCentroid_similarityRelabel h (decode_geometry p.1) v,
        ApproximantCovarianceFromBlockTransport.positiveSimilarity_sub]
    have hsub := gradientTransported_sub h1 h2
    intro v w
    rw [gatedVariation_of_mem m hg', gatedVariation_of_mem m hg', gatedVariation_of_mem m hg,
      gatedVariation_of_mem m hg]
    exact hsub v w
  · have hg' : (coupledSimilarity s u hs p).1 ∉ goodSet :=
      fun h' => hg ((mem_goodSet_iff_coupledSimilarity s u hs p).2 h')
    intro v w
    rw [gatedVariation_of_notMem m hg', gatedVariation_of_notMem m hg',
      gatedVariation_of_notMem m hg, gatedVariation_of_notMem m hg]
    simp

/-! ### The pathwise ownership data -/

/-- **The gated variation vanishes on the skeleton, pathwise.**  On the good set `φ_m` is
either a block interpolant (pinned to `b` on the skeleton) or the centroid field; off it the
gate closes. -/
theorem gatedVariation_eq_zero_of_mem_skeleton (m : ℕ) (hm : m ≠ 0) (p : CoupledSpace)
    (v : Vertex p.1.val) (hv : v ∈ skeleton (decode p.1) p.2.1 (m : ℝ)) :
    gatedVariation m p v = 0 := by
  by_cases hg : p.1 ∈ goodSet
  · rw [gatedVariation_eq_phi_sub m hg]
    show phi (decode p.1) p.2.1 m v - cellCentroid (decode p.1) v = 0
    by_cases hex : ∃ f, IsBlockInterpolation (decode p.1) p.2.1 m f
    · have hphi := phi_spec_of_exists (decode p.1) p.2.1 m hex
      rw [IsBlockInterpolation, if_neg hm] at hphi
      rw [hphi.1 v hv, sub_self]
    · rw [ApproximantCovarianceFromBlockTransport.phi_of_not_exists (decode p.1) p.2.1 m hex,
        sub_self]
  · exact gatedVariation_of_notMem m hg v

/-- **Cover-or-vanish**: the selected squares cover the plane on the good set, and off it the
gated variation vanishes. -/
theorem gatedVariation_eq_zero_of_not_cover (m : ℕ) (hm : m ≠ 0) (p : CoupledSpace)
    (hcov : ¬ SelectionCoversOn (decode p.1) p.2.1 (m : ℝ)) (v : Vertex p.1.val) :
    gatedVariation m p v = 0 := by
  by_cases hg : p.1 ∈ goodSet
  · exact absurd (selectionCoversOn_of_mem_goodSet hg p.2.1
      (Nat.cast_pos.2 (Nat.pos_of_ne_zero hm))) hcov
  · exact gatedVariation_of_notMem m hg v

/-- The ownership datum of the pairing of a coupled field with the gated variation. -/
noncomputable def variationOwnership (Ψ : ∀ p : CoupledSpace, Vertex p.1.val → Plane) (m : ℕ)
    (hm : m ≠ 0) : PairingOwnership coupledReRooting (m : ℝ) Ψ (gatedVariation m) :=
  gatedPairingOwnership coupledReRooting (m : ℝ) Ψ (gatedVariation m)
    (fun p hcov v => gatedVariation_eq_zero_of_not_cover m hm p hcov v)
    (fun p v hv => gatedVariation_eq_zero_of_mem_skeleton m hm p v hv)

/-! ### Label representations and measurability -/

/-- The label field of the gated variation. -/
noncomputable def variationLabel (m : ℕ) (p : CoupledSpace) (n : ℕ) : Plane :=
  if p.1 ∈ goodSet then
    gatedApproximant m (p.1, p.2.1) n - BlockInterpolantSelectionGate.slotCentroid p.1 n
  else 0

theorem gatedVariation_eq_label (m : ℕ) (p : CoupledSpace) (v : Vertex p.1.val) :
    gatedVariation m p v = variationLabel m p v.val := by
  unfold gatedVariation variationLabel
  by_cases hg : p.1 ∈ goodSet
  · rw [if_pos hg, if_pos hg, BlockInterpolantSelectionGate.slotCentroid_eq_cellCentroid]
    rfl
  · rw [if_neg hg, if_neg hg]

/-- The projection onto the environment and the passive grid. -/
def passiveMarked (p : CoupledSpace) : Env × Grid := (p.1, p.2.2)

theorem measurable_passiveMarked : Measurable passiveMarked :=
  measurable_fst.prodMk (measurable_snd.comp measurable_snd)

theorem measurable_variationLabel (m : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) (n : ℕ) :
    Measurable fun p : CoupledSpace => variationLabel m p n := by
  have h1 : Measurable fun p : CoupledSpace => gatedApproximant m (p.1, p.2.1) n :=
    (hmeas m n).comp measurable_blockMarked
  have h2 : Measurable fun p : CoupledSpace => BlockInterpolantSelectionGate.slotCentroid p.1 n :=
    (BlockInterpolantSelectionGate.measurable_slotCentroid n).comp measurable_fst
  have h3 : Measurable fun p : CoupledSpace =>
      gatedApproximant m (p.1, p.2.1) n - BlockInterpolantSelectionGate.slotCentroid p.1 n :=
    h1.sub h2
  exact Measurable.ite (measurable_fst measurableSet_goodSet) h3 measurable_const

/-! ### The two projections preserve the laws -/

section Law

variable (ν : Measure Env) [SFinite ν]

theorem measurePreserving_blockMarked :
    MeasurePreserving blockMarked (ν.prod (gridMeasure.prod gridMeasure)) (ν.prod gridMeasure) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hEq : blockMarked = Prod.map (id : Env → Env) (Prod.fst : Grid × Grid → Grid) := by
    funext p
    rfl
  rw [hEq]
  exact (MeasurePreserving.id ν).prod measurePreserving_fst

theorem measurePreserving_passiveMarked :
    MeasurePreserving passiveMarked (ν.prod (gridMeasure.prod gridMeasure))
      (ν.prod gridMeasure) := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hEq : passiveMarked = Prod.map (id : Env → Env) (Prod.snd : Grid × Grid → Grid) := by
    funext p
    rfl
  rw [hEq]
  exact (MeasurePreserving.id ν).prod measurePreserving_snd

/-- An almost-sure property of the environment lifts to the coupled law. -/
theorem ae_coupled_of_ae_env {P : Env → Prop} (h : ∀ᵐ e ∂ν, P e) :
    ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)), P p.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := ν)
    (ν := gridMeasure.prod gridMeasure)).tendsto_ae.eventually h

/-- An almost-sure property of a marked environment lifts to the coupled law along the block
grid. -/
theorem ae_coupled_of_ae_marked_block {P : MarkedEnvironment → Prop}
    (h : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridMeasure, P ω) :
    ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)), P (p.1, p.2.1) :=
  (measurePreserving_blockMarked ν).quasiMeasurePreserving.tendsto_ae.eventually h

/-- An almost-sure property of a marked environment lifts to the coupled law along the passive
grid. -/
theorem ae_coupled_of_ae_marked_passive {P : MarkedEnvironment → Prop}
    (h : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridMeasure, P ω) :
    ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)), P (p.1, p.2.2) :=
  (measurePreserving_passiveMarked ν).quasiMeasurePreserving.tendsto_ae.eventually h

end Law

/-! ### Finiteness of the expected specific energy of the gated variation -/

/-- The rooted specific-energy density of the zero field vanishes. -/
theorem rootedSpecificEnergyDensity_zero_field {V : Type*} [Countable V] (F : IndexedCells V)
    (z : Plane) : rootedSpecificEnergyDensity F (fun _ : V => (0 : Plane)) z = 0 := by
  cases hroot : rootAt F z with
  | none => simp [rootedSpecificEnergyDensity, hroot]
  | some v => simp [rootedSpecificEnergyDensity, specificEnergyDensity, hroot]

/-- `ρ_{gatedVariation} ≤ 2 ρ_{φ_m} + 2 ρ_b` pointwise. -/
theorem rootedSpecificEnergyDensity_gatedVariation_le (m : ℕ) (p : CoupledSpace) :
    rootedSpecificEnergyDensity (decode p.1) (gatedVariation m p) 0
      ≤ 2 * rootedSpecificEnergyDensity (decode p.1)
          (MarkedStageFieldCovariance.stageField m (p.1, p.2.1)) 0
        + 2 * rootedSpecificEnergyDensity (decode p.1) (cellCentroid (decode p.1)) 0 := by
  by_cases hg : p.1 ∈ goodSet
  · have hEq : gatedVariation m p = fun v =>
        MarkedStageFieldCovariance.stageField m (p.1, p.2.1) v - cellCentroid (decode p.1) v :=
      funext fun v => gatedVariation_of_mem m hg v
    rw [hEq]
    exact MarkedStageCoefficientScaling.rootedSpecificEnergyDensity_sub_le (decode p.1)
      (decode_geometry p.1) _ _ 0
  · have hEq : gatedVariation m p = fun _ => (0 : Plane) :=
      funext fun v => gatedVariation_of_notMem m hg v
    rw [hEq, rootedSpecificEnergyDensity_zero_field]
    exact zero_le

/-- The rooted specific energy of the centroid field is measurable in the environment. -/
theorem measurable_rootedSpecificEnergyDensity_cellCentroid :
    Measurable fun e : Env =>
      rootedSpecificEnergyDensity (decode e) (cellCentroid (decode e)) 0 := by
  have h := MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (id : Env → Env)) measurable_id
    (Ψ := fun e n => BlockInterpolantSelectionGate.slotCentroid e n)
    (fun n => BlockInterpolantSelectionGate.measurable_slotCentroid n)
  have h' : Measurable fun e : Env => rootedSpecificEnergyDensity (decode e)
      (fun v : Vertex e.val => BlockInterpolantSelectionGate.slotCentroid e v.val) 0 := h
  have hEq : (fun e : Env => rootedSpecificEnergyDensity (decode e)
        (fun v : Vertex e.val => BlockInterpolantSelectionGate.slotCentroid e v.val) 0)
      = fun e : Env => rootedSpecificEnergyDensity (decode e) (cellCentroid (decode e)) 0 := by
    funext e
    congr 1
    funext v
    exact BlockInterpolantSelectionGate.slotCentroid_eq_cellCentroid e v
  rw [hEq] at h'
  exact h'

section Finite

variable (ν : Measure Env) [IsProbabilityMeasure ν]

/-- The rooted specific energy of the gated stage field of the block grid is measurable on the
coupled space. -/
theorem measurable_rootedSpecificEnergyDensity_stageField_block (m : ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable fun p : CoupledSpace => rootedSpecificEnergyDensity (decode p.1)
      (MarkedStageFieldCovariance.stageField m (p.1, p.2.1)) 0 :=
  (MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
    (E := (Prod.fst : MarkedEnvironment → Env)) measurable_fst
    (Ψ := fun ω n => gatedApproximant m ω n) (fun n => hmeas m n)).comp measurable_blockMarked

/-- **The expected specific energy of the gated variation is finite**, from `e_m ≤ e_0 < ∞`
(`hproj`) and `s:lem:e0`. -/
theorem lintegral_rootedSpecificEnergyDensity_gatedVariation_ne_top (hν : MassTransport ν)
    (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν) (m : ℕ) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (gatedVariation m p) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞ := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hSmeasM : Measurable fun ω : MarkedEnvironment => rootedSpecificEnergyDensity (decode ω.1)
      (MarkedStageFieldCovariance.stageField m ω) 0 :=
    MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
      (E := (Prod.fst : MarkedEnvironment → Env)) measurable_fst
      (Ψ := fun ω n => gatedApproximant m ω n) (fun n => hmeas m n)
  have hS : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
      (MarkedStageFieldCovariance.stageField m (p.1, p.2.1)) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞ := by
    have h : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
        (MarkedStageFieldCovariance.stageField m (p.1, p.2.1)) 0
          ∂(ν.prod (gridMeasure.prod gridMeasure)))
        = ∫⁻ ω : MarkedEnvironment, rootedSpecificEnergyDensity (decode ω.1)
          (MarkedStageFieldCovariance.stageField m ω) 0 ∂(ν.prod gridMeasure) :=
      (measurePreserving_blockMarked ν).lintegral_comp hSmeasM
    rw [h]
    have hg : (∫⁻ ω : MarkedEnvironment, rootedSpecificEnergyDensity (decode ω.1)
        (MarkedStageFieldCovariance.stageField m ω) 0 ∂(ν.prod gridMeasure))
        = MarkedStageFieldCovariance.gatedStageEnergy ν m := rfl
    rw [hg, MarkedStageFieldCovariance.gatedStageEnergy_eq ν hν hFE m]
    exact (SpecificEnergyConvergence.markedStageEnergy_lt_top ν hν hFE hproj m).ne
  have hb : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (cellCentroid (decode p.1)) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞ := by
    have h : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (cellCentroid (decode p.1)) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure)))
        = ∫⁻ e, rootedSpecificEnergyDensity (decode e) (cellCentroid (decode e)) 0 ∂ν :=
      (MeasureTheory.measurePreserving_fst (μ := ν) (ν := gridMeasure.prod gridMeasure)).lintegral_comp
        measurable_rootedSpecificEnergyDensity_cellCentroid
    rw [h]
    obtain ⟨hle, hlt⟩ :=
      BaseSpecificEnergy.baseSpecificEnergy_le_two_mul_diamSqPiMoment_lt_top ν hν hFE.ne
    exact (lt_of_le_of_lt hle hlt).ne
  have hSmeas := measurable_rootedSpecificEnergyDensity_stageField_block m hmeas
  have hle : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (gatedVariation m p) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure)))
      ≤ ∫⁻ p, (2 * rootedSpecificEnergyDensity (decode p.1)
          (MarkedStageFieldCovariance.stageField m (p.1, p.2.1)) 0
        + 2 * rootedSpecificEnergyDensity (decode p.1) (cellCentroid (decode p.1)) 0)
          ∂(ν.prod (gridMeasure.prod gridMeasure)) :=
    lintegral_mono fun p => rootedSpecificEnergyDensity_gatedVariation_le m p
  rw [lintegral_add_left' (hSmeas.const_mul 2).aemeasurable, lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)] at hle
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by norm_num) hS, ENNReal.mul_ne_top (by norm_num) hb⟩) hle

end Finite

/-! ### The stagewise identity for a limiting potential of either grid -/

section Identity

variable (ν : Measure Env) [IsProbabilityMeasure ν]

/-- **`⟪Ψ, φ_m − b⟫_* = 0` on the coupled law**, for any coupled transported field `Ψ` with a
measurable label representation, finite expected specific energy and almost-sure full
rectangle orthogonality, at every positive stage `m`.  The variation is the gated `φ_m − b` of
the block grid. -/
theorem integral_pairing_gatedVariation_eq_zero (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (Ψ : ∀ p : CoupledSpace, Vertex p.1.val → Plane) (LΨ : CoupledSpace → ℕ → Plane)
    (hΨL : ∀ (p : CoupledSpace) (v : Vertex p.1.val), Ψ p v = LΨ p v.val)
    (hLmeas : ∀ n : ℕ, Measurable fun p : CoupledSpace => LΨ p n)
    (hΨt : CoupledTransportedField Ψ)
    (hΨfin : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (Ψ p) 0
      ∂(ν.prod (gridMeasure.prod gridMeasure))) ≠ ∞)
    (hFRO : ∀ᵐ p ∂(ν.prod (gridMeasure.prod gridMeasure)),
      FullRectangleOrthogonality (decode p.1) (Ψ p))
    (m : ℕ) (hm : m ≠ 0) :
    (∫ p, rootedPairingDensity (decode p.1) (Ψ p) (gatedVariation m p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure))) = 0 := by
  have : IsProbabilityMeasure gridMeasure := isProbabilityMeasure_gridMeasure
  have hMax := spatialMaximalBound_of_massTransport ν hν hFE
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hm)
  -- the almost-sure environment data
  have hgood : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)), p.1 ∈ goodSet :=
    ae_coupled_of_ae_env ν (ae_mem_goodSet ν hν hFE.ne)
  have hbdry : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      (0 : Plane) ∉ boundaryMask (decode p.1) :=
    ae_coupled_of_ae_env ν (Spatial.ae_notMem_boundaryMask_of_massTransport ν hν)
  have hcell : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      SpatialDiameterCellBounds (decode p.1) :=
    ae_coupled_of_ae_env ν
      (AlmostSureSpatialDiameterBounds.ae_spatialDiameterCellBounds_of_ballBound ν hν hFE.ne hMax)
  have hblockI : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      IsBlockInterpolation (decode p.1) p.2.1 m (phi (decode p.1) p.2.1 m) := by
    have h' : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridMeasure,
        IsBlockInterpolation (decode ω.1) ω.2 m (phi (decode ω.1) ω.2 m) := by
      filter_upwards [ae_blockInterpolation_clause ν hν hFE.ne hMax] with ω hω
      exact (hω.2 m).1
    exact ae_coupled_of_ae_marked_block ν h'
  have hsel : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      ∃ k : ℤ, OriginSelected (decode p.1) p.2.1 (m : ℝ) k := by
    have hcov : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
        (0 : Plane) ∉ uncoveredSet (decode p.1) :=
      ae_coupled_of_ae_env ν (ReflectedGMS.ae_zero_notMem_uncoveredSet ν hν)
    filter_upwards [hgood, hcov] with p hg hpcov
    exact originChainRegularOn_goodMarked.exists_originSelected'
      (ω := ((⟨p.1, hg⟩ : goodSet), p.2.1)) hpcov hmpos
  -- measurability of the coefficient
  have hcoeff : ∀ q : ℕ × ℕ, Measurable fun p : CoupledSpace =>
      pairCoeff p.1 (Ψ p) (gatedVariation m p) q := by
    intro q
    have hEq : (fun p : CoupledSpace => pairCoeff p.1 (Ψ p) (gatedVariation m p) q)
        = fun p : CoupledSpace => pairCoeff p.1 (fun v => LΨ p v.val)
          (fun v => variationLabel m p v.val) q := by
      funext p
      have hA : Ψ p = fun v : Vertex p.1.val => LΨ p v.val := funext fun v => hΨL p v
      have hB : gatedVariation m p = fun v : Vertex p.1.val => variationLabel m p v.val :=
        funext fun v => gatedVariation_eq_label m p v
      rw [hA, hB]
    rw [hEq]
    exact measurable_pairCoeff_of_labels measurable_fst hLmeas (measurable_variationLabel m hmeas) q
  -- measurability and finiteness of the two energies
  have hΨmeas : Measurable fun p : CoupledSpace =>
      rootedSpecificEnergyDensity (decode p.1) (Ψ p) 0 := by
    have h := MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity
      (E := (Prod.fst : CoupledSpace → Env)) measurable_fst (Ψ := LΨ) hLmeas
    have hEq : (fun p : CoupledSpace => rootedSpecificEnergyDensity (decode p.1)
        (fun v : Vertex p.1.val => LΨ p v.val) 0)
        = fun p : CoupledSpace => rootedSpecificEnergyDensity (decode p.1) (Ψ p) 0 := by
      funext p
      have hA : Ψ p = fun v : Vertex p.1.val => LΨ p v.val := funext fun v => hΨL p v
      rw [hA]
    rw [hEq] at h
    exact h
  have hHfin := lintegral_rootedSpecificEnergyDensity_gatedVariation_ne_top ν hν hFE hmeas hproj m
  have hpfin := lintegral_rootEndpointDensity_ne_top_of_sign (posField (variationOwnership Ψ m hm))
    (fun p q => Or.inl (posField_weight (variationOwnership Ψ m hm) p q)) hbdry hΨmeas.aemeasurable
    hΨfin hHfin
  have hmfin := lintegral_rootEndpointDensity_ne_top_of_sign (negField (variationOwnership Ψ m hm))
    (fun p q => Or.inr (negField_weight (variationOwnership Ψ m hm) p q)) hbdry hΨmeas.aemeasurable
    hΨfin hHfin
  -- the almost-sure block data
  have hdata : ∀ᵐ p : CoupledSpace ∂(ν.prod (gridMeasure.prod gridMeasure)),
      (Summable fun q : ℕ × ℕ => ((posField (variationOwnership Ψ m hm)).ownedByOriginBlock p).indicator
        (pairCoeff p.1 (Ψ p) (gatedVariation m p)) q) ∧
      (∑' q : ℕ × ℕ, ((posField (variationOwnership Ψ m hm)).ownedByOriginBlock p).indicator
        (pairCoeff p.1 (Ψ p) (gatedVariation m p)) q) = 0 := by
    filter_upwards [hgood, hcell, hblockI, hFRO, hsel] with p hg hW hphi hF hs
    have hgeom : Geometry (decode p.1) := decode_geometry p.1
    have hblock : Selected (decode p.1) p.2.1 (m : ℝ)
        (blockSquareIndex (decode p.1) p.2.1 (m : ℝ)) := originSelected_blockLevel hs
    have hΨE : vectorEnergy (restrictGraph (decode p.1).graph
        (patchVertices (decode p.1) (square p.2.1 (blockSquareIndex (decode p.1) p.2.1 (m : ℝ)))))
        (fun v => Ψ p v.1) < ∞ :=
      (hF (square p.2.1 (blockSquareIndex (decode p.1) p.2.1 (m : ℝ)))).1
    have hφE : vectorEnergy (restrictGraph (decode p.1).graph
        (patchVertices (decode p.1) (square p.2.1 (blockSquareIndex (decode p.1) p.2.1 (m : ℝ)))))
        (fun v => phi (decode p.1) p.2.1 m v.1) < ∞ :=
      (centroidTraceMinimizer_of_isBlockInterpolation (decode p.1) p.2.1 hm hphi hblock).1
    have hbE : vectorEnergy (restrictGraph (decode p.1).graph
        (patchVertices (decode p.1) (square p.2.1 (blockSquareIndex (decode p.1) p.2.1 (m : ℝ)))))
        (fun v => cellCentroid (decode p.1) v.1) < ∞ :=
      vectorEnergy_cellCentroid_lt_top_of_localPiMass (decode p.1) hgeom _
        (localDiameterPiMass_patchVertices (decode p.1)
          (spatialDiameterPiBounds_of_cellBounds (decode p.1) hW) _)
    have hHE : vectorEnergy (restrictGraph (decode p.1).graph
        (patchVertices (decode p.1) (square p.2.1 (blockSquareIndex (decode p.1) p.2.1 (m : ℝ)))))
        (fun v => gatedVariation m p v.1) < ∞ := by
      rw [gatedVariation_eq_phi_sub m hg]
      exact vectorEnergy_lt_top_of_coord _ fun i =>
        NestedEnergyProjections.hasFiniteEnergy_coord_sub _ hbE hφE i
    have horth : vectorPairing (restrictGraph (decode p.1).graph
        (patchVertices (decode p.1) (square p.2.1 (blockSquareIndex (decode p.1) p.2.1 (m : ℝ)))))
        (fun v => Ψ p v.1) (fun v => gatedVariation m p v.1) = 0 :=
      (hF (square p.2.1 (blockSquareIndex (decode p.1) p.2.1 (m : ℝ)))).2
        (fun v => gatedVariation m p v.1)
        ⟨hHE, fun v hv => gatedVariation_eq_zero_of_mem_skeleton m hm p v.1
          (mem_skeleton_of_mem_boundaryVertices (decode p.1) p.2.1 (m : ℝ) hblock hv)⟩
    exact ⟨summable_indicator_ownedByOriginBlock_of_energies (variationOwnership Ψ m hm)
        (fun _ _ => rfl) (fun p v hv => gatedVariation_eq_zero_of_mem_skeleton m hm p v hv) p hs
        hΨE hHE,
      tsum_indicator_ownedByOriginBlock_eq_zero_of_orthogonality (variationOwnership Ψ m hm)
        (fun _ _ => rfl) (fun p v hv => gatedVariation_eq_zero_of_mem_skeleton m hm p v hv) p hs
        hΨE hHE horth⟩
  exact integral_rootedPairingDensity_eq_zero_coupled (m : ℝ) Ψ (gatedVariation m)
    (variationOwnership Ψ m hm) (fun _ _ => rfl) ν hν hΨt
    (coupledTransportedField_gatedVariation m) hcoeff hsel hpfin hmfin
    (hdata.mono fun p h => h.1) (hdata.mono fun p h => h.2) hbdry

/-! ### The two instances -/

/-- The label field of the cross potential. -/
noncomputable def crossLabel (ms : ℕ → ℕ) (p : CoupledSpace) (n : ℕ) : Plane :=
  markedDifferenceField ms (p.1, p.2.2) (Nat.pair (baseLabel p.1) n)

/-- The label field of the block potential. -/
noncomputable def blockLabel (ms : ℕ → ℕ) (p : CoupledSpace) (n : ℕ) : Plane :=
  markedDifferenceField ms (p.1, p.2.1) (Nat.pair (baseLabel p.1) n)

theorem crossPotential_eq_label (ms : ℕ → ℕ) (p : CoupledSpace) (v : Vertex p.1.val) :
    crossPotential ms p v = crossLabel ms p v.val := rfl

theorem blockPotential_eq_label (ms : ℕ → ℕ) (p : CoupledSpace) (v : Vertex p.1.val) :
    blockPotential ms p v = blockLabel ms p v.val := rfl

theorem measurable_crossLabel (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) (n : ℕ) :
    Measurable fun p : CoupledSpace => crossLabel ms p n :=
  (measurable_markedPotentialLabel ms hmeas n).comp measurable_passiveMarked

theorem measurable_blockLabel (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) (n : ℕ) :
    Measurable fun p : CoupledSpace => blockLabel ms p n :=
  (measurable_markedPotentialLabel ms hmeas n).comp measurable_blockMarked

/-- The expected specific energy of the marked potential, transported to the coupled law along
either projection. -/
theorem lintegral_rootedSpecificEnergyDensity_crossPotential (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (crossPotential ms p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ ω : MarkedEnvironment,
          rootedSpecificEnergyDensity (decode ω.1) (markedPotential ms ω) 0 ∂ν.prod gridMeasure :=
  (measurePreserving_passiveMarked ν).lintegral_comp
    (measurable_rootedSpecificEnergyDensity_markedPotential ms hmeas)

theorem lintegral_rootedSpecificEnergyDensity_blockPotential (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (blockPotential ms p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure)))
      = ∫⁻ ω : MarkedEnvironment,
          rootedSpecificEnergyDensity (decode ω.1) (markedPotential ms ω) 0 ∂ν.prod gridMeasure :=
  (measurePreserving_blockMarked ν).lintegral_comp
    (measurable_rootedSpecificEnergyDensity_markedPotential ms hmeas)

/-- **The cross identity** `⟪Φ², φ_m¹ − b⟫_* = 0`: the limiting potential of the passive grid
against the gated stage variation of the block grid, at every positive stage. -/
theorem integral_crossPairing_eq_zero (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (m : ℕ) (hm : m ≠ 0) :
    (∫ p, rootedPairingDensity (decode p.1) (crossPotential ms p) (gatedVariation m p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure))) = 0 := by
  have hspec := SpecificEnergyConvergence.markedSpecificEnergyConvergence_of_nestedProjection ν hν
    hFE hmeas hproj ms hms hconv
  have hdens := markedDensityMeasurability_of_massTransport ν hν hFE.ne ms hmeas
  refine integral_pairing_gatedVariation_eq_zero ν hν hFE hmeas hproj (crossPotential ms)
    (crossLabel ms) (crossPotential_eq_label ms) (measurable_crossLabel ms hmeas)
    (coupledTransportedField_crossPotential ms) ?_ ?_ m hm
  · rw [lintegral_rootedSpecificEnergyDensity_crossPotential ν ms hmeas]
    exact (lintegral_rootedSpecificEnergyDensity_markedPotential_lt_top ν ms hdens hspec).ne
  · have hharm := MarkedRectangleOrthogonalityProducer.markedHarmonicity_of_patchConvergence ν hν
      hFE ms hms hpatch
    have h' : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridMeasure,
        FullRectangleOrthogonality (decode ω.1) (markedPotential ms ω) := by
      filter_upwards [hharm] with ω hω
      exact hω.1
    exact ae_coupled_of_ae_marked_passive ν h'

/-- **The same-grid identity** `⟪Φ¹, φ_m¹ − b⟫_* = 0`: the limiting potential of the block grid
against its own gated stage variation, at every positive stage. -/
theorem integral_blockPairing_eq_zero (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hproj : SpecificEnergyConvergence.MarkedNestedProjectionBound ν)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (m : ℕ) (hm : m ≠ 0) :
    (∫ p, rootedPairingDensity (decode p.1) (blockPotential ms p) (gatedVariation m p) 0
        ∂(ν.prod (gridMeasure.prod gridMeasure))) = 0 := by
  have hspec := SpecificEnergyConvergence.markedSpecificEnergyConvergence_of_nestedProjection ν hν
    hFE hmeas hproj ms hms hconv
  have hdens := markedDensityMeasurability_of_massTransport ν hν hFE.ne ms hmeas
  refine integral_pairing_gatedVariation_eq_zero ν hν hFE hmeas hproj (blockPotential ms)
    (blockLabel ms) (blockPotential_eq_label ms) (measurable_blockLabel ms hmeas)
    (coupledTransportedField_blockPotential ms) ?_ ?_ m hm
  · rw [lintegral_rootedSpecificEnergyDensity_blockPotential ν ms hmeas]
    exact (lintegral_rootedSpecificEnergyDensity_markedPotential_lt_top ν ms hdens hspec).ne
  · have hharm := MarkedRectangleOrthogonalityProducer.markedHarmonicity_of_patchConvergence ν hν
      hFE ms hms hpatch
    have h' : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridMeasure,
        FullRectangleOrthogonality (decode ω.1) (markedPotential ms ω) := by
      filter_upwards [hharm] with ω hω
      exact hω.1
    exact ae_coupled_of_ae_marked_block ν h'

end Identity

end ReflectedGMS.CopyDifferenceCrossPairing
