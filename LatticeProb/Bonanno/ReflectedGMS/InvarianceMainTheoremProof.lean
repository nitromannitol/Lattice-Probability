/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.InvarianceMainTheoremProof at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CellRootedFrontier
import LatticeProb.Bonanno.ReflectedGMS.Limit.InteriorRepresentative
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedRegenAllStarts
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowSlotShift
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RatShiftBridgeProof

/-!
# The reflected invariance main theorem, with no hypotheses

`InvarianceMainStatement.ReflectedInvarianceMainTheorem` is the manuscript's complete process
target:

```
∀ (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValid P),
  AmbientMassTransport P hP → FiniteEnergyMoment (validLaw P hP) →
  AmbientEnvironmentErgodic P hP → ReflectedInvarianceConclusions (validLaw P hP)
```

`reflectedInvarianceMainTheorem` proves it by one application of the cell-rooted frontier
`CellRootedFrontier.reflectedInvarianceConclusions_validLaw_cellRootedFrontier` at the interior
representative `InteriorRepresentative.interiorField` (which discharges the frontier's `hz`), with
the following inputs:

* gate data from MTP + (FE): `CellRootedFrontierInterior.exists_gate_interiorField`;
* the time transport `hplain`, the manuscript's `p:lem:timeMTP` (tex:1379-1397):
  `CellRootedTimeMTPFlow.cellRootedPlainTransport_validLaw_interiorField`;
* joint ergodicity `hregen`, the manuscript's `p:lem:regeninvariant` (tex:1494-1511), from the
  rational-shift bridge `hbr`: `CellRootedRegenAllStartsWeld.hregen_validLaw_interior_of_ratShiftBridge`;
* `hbr` itself: `RatShiftBridgeProof.ratShiftBridgeOn_interiorField`.

Folded on 2026-09-18 (simplification Packet D) from the former modules
`Limit/CellRootedFrontierInterior`, `Temporal/CellRootedTimeMTPFlow`,
`Temporal/CellRootedRegenAllStartsWeld` and `InvarianceMainTheoremFinal`.  The declarations keep
their names; the three pure-application welds that only threaded arguments
(`CellRootedFrontierInterior.reflectedInvarianceConclusions_validLaw_interior`,
`CellRootedRegenAllStartsWeld.reflectedInvarianceConclusions_validLaw_interior_of_ratShiftBridge`,
`InvarianceMainTheoremFinal.reflectedInvarianceMainTheorem_of_ratShiftBridge`) are inlined into
`reflectedInvarianceMainTheorem`.
-/

set_option autoImplicit false

/-! ## Gate data at the interior representative

`Limit/InteriorRepresentative.interiorField` is a measurable `CellField` that is interior-off-mask,
translation covariant and dilation covariant at every valid environment, so it discharges the
frontier's `hz`; gate data for it exist from MTP + (FE). -/

section FrontierInterior

open MeasureTheory Filter Set ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.CellRootedFrontierInterior

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open StatementIngredients AreaClocks InvarianceMainStatement QuenchedFormulation RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.TwoSidedRegenerationFlowGrid
open ReflectedGMS.FlowCodingKernel ReflectedGMS.FlowCodingDensity
open ReflectedGMS.CellRootedEncodingRepair ReflectedGMS.CellRootedFrontier
open ReflectedGMS.InteriorRepresentative
open ReflectedGMS.GridAveragedConstantReduction

/-- Gate data for the interior representative, from MTP + (FE). -/
theorem exists_gate_interiorField (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    ∃ G : Set Env, MeasurableSet G ∧ ν Gᶜ = 0 ∧ (∀ e ∈ G, EnvironmentAreaClockAdmissible e) ∧
      ExtensionGate interiorField G :=
  exists_flowKernel_gate_of_interiorOffMask ν hmt hFE interiorOffMask_interiorField

end ReflectedGMS.CellRootedFrontierInterior

end FrontierInterior

/-! ## `hplain`: `p:lem:timeMTP` at the cell-rooted law

The weld of the manuscript proof of `p:lem:timeMTP` (tex:1379-1397): the abstract proof
`CellRootedTimeMTP.cellRootedPlainTransport_of_startKernels` (spatial transport `T(H,w,z)` from
the time functional, its degree `-2`, spatial MTP, and on the incoming side the shift invariance
of `ℚ_H` plus Tonelli), instantiated with the all-starts kernel at the similarity-closed gate
(`FlowSlotKernel.closedSlotKernel`: exact similarity covariance, fixed-time definedness, start) and
the two-sided real-time shift invariance of `ℚ_H` on the carrier
(`FlowSlotShift.measurePreserving_codingShift_closedSlotKernel`).  The bridge kernel at any conull
admissible gate gives the same annealed law (`FlowCodingFrontier.compProd_flowKernel_congr`), so
the result holds for every gate.

Covariance of `z` is necessary (P2 handoff §2: counterexample for a non-covariant field).  The
known trap — the transport is false at a fixed environment with a single start — is avoided: the
only fixed-environment statement is the shift invariance of the σ-finite ALL-starts mixture `ℚ_H`,
and the passage to the single root start happens only after spatial MTP. -/

section TimeMTPFlow

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace ReflectedGMS.CellRootedTimeMTPFlow

open Code EnvironmentFields EnvironmentLaws RootDensities HarmonicLawIngredients
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.FlowCodingKernel ReflectedGMS.CellRootedTemporalTransport
open ReflectedGMS.CellRootedTimeMTP ReflectedGMS.FlowSlotKernel ReflectedGMS.FlowSlotShift
open ReflectedGMS.SimilarityClosedGate ReflectedGMS.ParabolicTransport
open ReflectedGMS.CellRootedEncodingRepair

/-- **`p:lem:timeMTP` at the cell-rooted law, at the similarity-closed gate.** -/
theorem cellRootedPlainTransport_closedGate (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (z : CellField)
    (hz : IsCellRepresentative z) (hzcov : RepSimilarityCovariant z.value) :
    CellRootedPlainTransport (ν ⊗ₘ flowKernel z similarityClosedGate
      measurableSet_similarityClosedGate (fun _ he => environmentAreaClockAdmissible_of_mem he)
      (extensionGateAll_similarityClosedGate z hz).extensionGate) := by
  have hGae : ∀ᵐ e ∂ν, e ∈ similarityClosedGate := ae_mem_similarityClosedGate ν hmt hFE
  refine cellRootedPlainTransport_of_startKernels ν hmt _ (closedSlotKernel z hz)
    similarityClosedGate measurableSet_similarityClosedGate mem_similarityClosedGate_iff_target
    ?_ ?_ ?_ ?_ ?_
  · intro e he n hn s u hs
    exact (map_simCoding_closedSlotKernel z hz hzcov hs u he hn).symm
  · filter_upwards [hGae] with e he
    refine ⟨he, fun v₀ hv₀ => ?_⟩
    rw [flowKernel_apply_eq_flowSlotKernel (hext := extensionGateAll_similarityClosedGate z hz),
      rootLabel_of_some hv₀]
    rfl
  · filter_upwards [hGae] with e he v₀ _
    exact ae_volume_notVertex_flowSlotKernel ⟨he, v₀.property⟩
  · filter_upwards [hGae] with e he r
    exact measurePreserving_codingShift_closedSlotKernel z hz he r
  · filter_upwards [hGae] with e he v
    exact ae_flowSlotKernel_start ⟨he, v.property⟩

/-- **`CellRootedPlainTransport (ν ⊗ₘ κF)` at every gate**, from MTP, (FE), and a
cell-representative field covariant under translations and dilations. -/
theorem cellRootedPlainTransport_flowKernel (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (z : CellField)
    (hz : IsCellRepresentative z) (hzT : RepTranslationCovariant z.value)
    (hzD : RepDilationCovariant z.value) {G : Set Env} (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGate z G)
    (hGc : ν Gᶜ = 0) :
    CellRootedPlainTransport (ν ⊗ₘ flowKernel z G hG hwalk hext) := by
  rw [FlowCodingFrontier.compProd_flowKernel_congr ν hG measurableSet_similarityClosedGate hwalk
    (fun _ he => environmentAreaClockAdmissible_of_mem he) hext
    (extensionGateAll_similarityClosedGate z hz).extensionGate hGc
    (measure_compl_similarityClosedGate ν hmt hFE)]
  exact cellRootedPlainTransport_closedGate ν hmt hFE z hz
    (repSimilarityCovariant_of_covariant hzT hzD)

/-- **The frontier binder `hplain` at the interior representative**, with no input beyond the
frontier's own (MTP, FE, gate data). -/
theorem cellRootedPlainTransport_validLaw_interiorField (P : Measure RawCode)
    [IsProbabilityMeasure P] (hP : SupportedOnValid P) (hmt : AmbientMassTransport P hP)
    (hFE : FiniteEnergyMoment (validLaw P hP)) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hext : ExtensionGate InteriorRepresentative.interiorField G)
    (hGc : validLaw P hP Gᶜ = 0) :
    CellRootedPlainTransport
      (validLaw P hP ⊗ₘ flowKernel InteriorRepresentative.interiorField G hG hwalk hext) :=
  cellRootedPlainTransport_flowKernel (validLaw P hP) hmt hFE InteriorRepresentative.interiorField
    InteriorRepresentative.isCellRepresentative_interiorField
    InteriorRepresentative.repTranslationCovariant_interiorField
    InteriorRepresentative.repDilationCovariant_interiorField hG hwalk hext hGc

end ReflectedGMS.CellRootedTimeMTPFlow

end TimeMTPFlow

/-! ## `hregen` from the rational-shift bridge

`CellRootedRegenAllStarts.regenerativeInvariance_validLaw_interior_allStarts` proves the frontier
binder `hregen` (manuscript `p:lem:regeninvariant`, tex:1494-1511, through the all-starts laws) from
an all-starts family `K` with (i) the fibre shape `SlotFibreShape`, (ii) exact similarity covariance
`SlotSimilarityCovariantOn`, (iii) two-sided real-time shift invariance of `Σ_v a_v K_v(e)`, and
(iv) the rational-shift bridge `RatShiftBridgeOn`.  Here (i)-(iii) are discharged at the closed-gate
all-starts kernel `FlowSlotKernel.closedSlotKernel interiorField …`: (i) is
`FlowSlotKernel.slotFibre_of_live` (definitional); (ii) is
`FlowSlotKernel.map_simCoding_closedSlotKernel`; (iii) is
`FlowSlotShift.measurePreserving_codingShift_closedSlotKernel`, at every gate environment, hence
a.s. (the gate is conull under MTP + (FE)). -/

section RegenAllStartsWeld

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CellRootedRegenAllStartsWeld

open Code EnvironmentLaws EnvironmentFields
open ReflectedGMS.TwoSidedRegenerationFlow ReflectedGMS.FlowCodingKernel
open ReflectedGMS.CellRootedEncodingRepair
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.HarmonicLawIngredients
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.CellRootedRegenAllStarts
open HarmonicMainStatement StatementIngredients InvarianceMainStatement

/-- **(i) The fibre shape of the closed-gate all-starts kernel** (definitional). -/
theorem slotFibreShape_closedSlotKernel (z : CellField) (hz : IsCellRepresentative z) :
    SlotFibreShape z SimilarityClosedGate.similarityClosedGate
      (FlowSlotKernel.closedSlotKernel z hz) := fun e he v =>
  FlowSlotKernel.slotFibre_of_live (z := z) (G := SimilarityClosedGate.similarityClosedGate)
    ⟨he, v.property⟩

/-- **(ii) Exact similarity covariance of the closed-gate all-starts kernel.** -/
theorem slotSimilarityCovariantOn_closedSlotKernel (z : CellField) (hz : IsCellRepresentative z)
    (hzcov : FlowSlotKernel.RepSimilarityCovariant z.value) :
    SlotSimilarityCovariantOn SimilarityClosedGate.similarityClosedGate
      (FlowSlotKernel.closedSlotKernel z hz) := fun _ he _ hn _ u hs =>
  (FlowSlotKernel.map_simCoding_closedSlotKernel z hz hzcov hs u he hn).symm

/-- **`hregen` at the cell-rooted law from the rational-shift bridge alone**: the frontier binder
of `CellRootedFrontier.reflectedInvarianceConclusions_validLaw_cellRootedFrontier` at the interior
representative, in its exact shape.  Conditional on `hbr` (the rational-shift bridge at every live
gate environment), which `RatShiftBridgeProof.ratShiftBridgeOn_interiorField` proves. -/
theorem hregen_validLaw_interior_of_ratShiftBridge (P : Measure RawCode)
    [IsProbabilityMeasure P] (hP : SupportedOnValid P) (hmt : AmbientMassTransport P hP)
    (hFE : FiniteEnergyMoment (validLaw P hP)) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hext : ExtensionGate InteriorRepresentative.interiorField G)
    (hGc : validLaw P hP Gᶜ = 0)
    (hbr : RatShiftBridgeOn InteriorRepresentative.interiorField
      SimilarityClosedGate.similarityClosedGate SimilarityClosedGate.measurableSet_similarityClosedGate
      (fun _ he => SimilarityClosedGate.environmentAreaClockAdmissible_of_mem he)) :
    RegenerativeInvariance
      ((validLaw P hP ⊗ₘ flowKernel InteriorRepresentative.interiorField G hG hwalk hext).map
        cellRoot) reRootFlow reScale Prod.fst := by
  have hC := SimilarityClosedGate.measure_compl_similarityClosedGate (validLaw P hP) hmt hFE
  refine regenerativeInvariance_validLaw_interior_allStarts P hP hmt hFE G hG hwalk hext hGc
    (FlowSlotKernel.closedSlotKernel InteriorRepresentative.interiorField
      InteriorRepresentative.isCellRepresentative_interiorField)
    (slotFibreShape_closedSlotKernel _ _)
    (slotSimilarityCovariantOn_closedSlotKernel _ _
      FlowSlotKernel.repSimilarityCovariant_interiorField) ?_ hbr
  have hGae : ∀ᵐ e ∂validLaw P hP, e ∈ SimilarityClosedGate.similarityClosedGate := ae_iff.2 hC
  filter_upwards [hGae] with e he
  exact fun r => FlowSlotShift.measurePreserving_codingShift_closedSlotKernel _ _ he r

end ReflectedGMS.CellRootedRegenAllStartsWeld

end RegenAllStartsWeld

/-! ## Main theorem 2 -/

namespace ReflectedGMS.InvarianceMainTheoremProof

open MeasureTheory
open Code EnvironmentLaws InvarianceMainStatement

/-- **Main theorem 2** (`ReflectedInvarianceMainTheorem`): for every supported probability law of
raw codes satisfying mass transport, finite energy and ambient ergodicity, the reflected
invariance conclusions hold for the valid law. -/
theorem reflectedInvarianceMainTheorem : ReflectedInvarianceMainTheorem := by
  intro P _ hP hmt hFE herg
  obtain ⟨G, hG, hGc, hwalk, hext⟩ :=
    CellRootedFrontierInterior.exists_gate_interiorField (validLaw P hP) hmt hFE
  exact CellRootedFrontier.reflectedInvarianceConclusions_validLaw_cellRootedFrontier P hP hmt hFE
    herg InteriorRepresentative.interiorField G hG hwalk hext hGc
    (CellRootedTimeMTPFlow.cellRootedPlainTransport_validLaw_interiorField P hP hmt hFE G hG hwalk
      hext hGc)
    (CellRootedRegenAllStartsWeld.hregen_validLaw_interior_of_ratShiftBridge P hP hmt hFE G hG
      hwalk hext hGc RatShiftBridgeProof.ratShiftBridgeOn_interiorField)
    ⟨InteriorRepresentative.interiorOffMask_interiorField,
      InteriorRepresentative.repTranslationCovariant_interiorField,
      InteriorRepresentative.repDilationCovariant_interiorField⟩

end ReflectedGMS.InvarianceMainTheoremProof
