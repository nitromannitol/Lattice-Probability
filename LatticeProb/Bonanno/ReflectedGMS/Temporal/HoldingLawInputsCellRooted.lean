/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.HoldingLawInputsCellRooted at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.HoldingDataFlowSpace
import LatticeProb.Bonanno.ReflectedGMS.Temporal.HoldingIntervalFiniteness

/-!
# `HoldingLawInputs` at the cell-rooted law

`HoldingDataFlowSpace.scaledRootChainSystemOn_cellRooted_of_plainTransport_holding` carries the
named input

  `HoldingLawInputs Q` :=
    `(∀ᵐ ω ∂Q, ω.2.1.toFun 0 ≠ ⊤) ∧ (∀ᵐ ω ∂Q, volume {s : ℝ | ω.2.1.toFun s = ⊤} = 0) ∧`
    `  (∀ᵐ ω ∂Q, ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞)`

at `Q = (ν ⊗ₘ κF).map cellRoot`.  This module discharges it.

* `cellRoot_label`: the cell-rooted encoding relabels the label path by the injective
  `simLabel 1 (ω.2.2.toFun 0) one_pos ω.1` and does NOT change its time parametrisation.  Hence
  `cellRoot` preserves the cemetery times (`cellRoot_label_ne_top_iff`) and the holding lengths
  (`cellRoot_holdLen`, `LabelHoldingIntervals.holdLen_of_shift` at shift `0`), so all three clauses
  are *pointwise* invariant under it and transfer through `ae_map_iff`.
* `holdingLawInputs_of_fixed`: on any s-finite law, fixed-time definedness at EVERY real time plus
  bounded holding intervals give the three clauses — the middle one by Tonelli
  (`Measure.ae_ae_comm` against `CadlagPath.measurable_eval_uncurry`).
* `holdingLawInputs_cellRooted`: **the input, discharged** at the actual cell-rooted law, from
  `MassTransport ν` and `ν Gᶜ = 0` alone.  Its two ingredients are
  `CellRootedTemporalTransport.ae_label_ne_top_flowKernel` (fixed-time definedness of the area walk,
  both halves) and `HoldingIntervalFiniteness.ae_holdLen_ne_top_flowKernel` (the walk leaves every
  vertex at arbitrarily large times, in both time directions).
* `scaledRootChainSystemOn_cellRooted_of_plainTransport_holding'`: the consumer join — `hsys` at the
  cell-rooted law in the singular setting from `hplain` and the gate data alone.

Nothing here certifies `CellRootedPlainTransport`, `p:lem:regeninvariant` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.HoldingLawInputsCellRooted

open Code EnvironmentFields EnvironmentLaws RootDensities HarmonicLawIngredients
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationFlowGrid
open ReflectedGMS.FlowCodingLine ReflectedGMS.FlowCodingKernel
open ReflectedGMS.CellRootedEncodingRepair ReflectedGMS.CellRootedTemporalTransport
open ReflectedGMS.LabelHoldingIntervals
open ReflectedGMS.HoldingIntervalsSubmacroscopic ReflectedGMS.HoldingDataFlowSpace
open ReflectedGMS.HoldingIntervalFiniteness
open ReflectedGMS.SupTypeTimeBlocks ReflectedGMS.SupTypeBlockSystem
open ReflectedGMS.ScaledRootChainGated

/-! ## 1. The cell-rooted encoding relabels the label path without changing the time -/

/-- The label path of the cell-rooted encoding is the relabelling of the original one by the
frame's label map, at the SAME time. -/
theorem cellRoot_label (ω : FlowSpace) (t : ℝ) :
    (cellRoot ω).2.1.toFun t
      = liftLabel (simLabel 1 (ω.2.2.toFun 0) one_pos ω.1) (ω.2.1.toFun t) := by
  rw [cellRoot_eq_reFrame]
  rfl

theorem cellRoot_label_ne_top_iff (ω : FlowSpace) (t : ℝ) :
    (cellRoot ω).2.1.toFun t ≠ ⊤ ↔ ω.2.1.toFun t ≠ ⊤ := by
  rw [cellRoot_label]
  exact not_congr (liftLabel_eq_top_iff _ _)

/-- The cell-rooted encoding preserves the holding lengths. -/
theorem cellRoot_holdLen (ω : FlowSpace) (s : ℝ) :
    holdLen (cellRoot ω).2.1 s = holdLen ω.2.1 s := by
  have h := holdLen_of_shift (Y := ω.2.1) (Y' := (cellRoot ω).2.1)
    (σ := simLabel 1 (ω.2.2.toFun 0) one_pos ω.1) (r := 0) (simLabel_injective _ _ _ _)
    (fun t => by rw [add_zero]; exact cellRoot_label ω t) s
  rwa [add_zero] at h

/-! ## 2. Transfer of the three clauses through `cellRoot` -/

theorem ae_label_ne_top_map_cellRoot {P : Measure FlowSpace}
    (hP : ∀ t : ℝ, ∀ᵐ ω ∂P, ω.2.1.toFun t ≠ ⊤) (t : ℝ) :
    ∀ᵐ ω ∂(P.map cellRoot), ω.2.1.toFun t ≠ ⊤ := by
  refine (ae_map_iff measurable_cellRoot.aemeasurable
    (measurableSet_label_ne_top t)).2 ?_
  filter_upwards [hP t] with ω hω
  exact (cellRoot_label_ne_top_iff ω t).2 hω

theorem ae_holdBounded_map_cellRoot {P : Measure FlowSpace} (hP : ∀ᵐ ω ∂P, ω ∈ HoldBounded) :
    ∀ᵐ ω ∂(P.map cellRoot), ω ∈ HoldBounded := by
  refine (ae_map_iff measurable_cellRoot.aemeasurable measurableSet_holdBounded).2 ?_
  filter_upwards [hP] with ω hω q hq
  rw [cellRoot_holdLen]
  exact hω q ((cellRoot_label_ne_top_iff ω (q : ℝ)).1 hq)

/-! ## 3. The three clauses from fixed-time definedness and bounded holding intervals -/

/-- **`HoldingLawInputs` from the two walk-level facts.**  The middle clause is Tonelli applied to
the fixed-time clause: `(ω, t) ↦ Y_t(ω)` is jointly measurable on the càdlàg carrier
(`CadlagPath.measurable_eval_uncurry`), so a.e. `t` being a.s. a vertex time gives a.s. a
Lebesgue-null set of cemetery times. -/
theorem holdingLawInputs_of_fixed {Q : Measure FlowSpace} [SFinite Q]
    (hfix : ∀ t : ℝ, ∀ᵐ ω ∂Q, ω.2.1.toFun t ≠ ⊤)
    (hhold : ∀ᵐ ω ∂Q, ∀ q : ℚ, ω.2.1.toFun q ≠ ⊤ → holdLen ω.2.1 q ≠ ∞) :
    HoldingLawInputs Q := by
  refine ⟨hfix 0, ?_, hhold⟩
  have hS : MeasurableSet {p : FlowSpace × ℝ | p.1.2.1.toFun p.2 ≠ ⊤} :=
    ((CadlagPath.measurable_eval_uncurry).comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
      (measurableSet_singleton ⊤).compl
  have h : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ ω ∂Q, ω.2.1.toFun t ≠ ⊤ :=
    Filter.Eventually.of_forall hfix
  have h' := (Measure.ae_ae_comm (p := fun (ω : FlowSpace) (t : ℝ) => ω.2.1.toFun t ≠ ⊤) hS).2 h
  filter_upwards [h'] with ω hω
  rw [ae_iff] at hω
  simpa only [ne_eq, not_not] using hω

/-! ## 4. The input, discharged at the actual cell-rooted law -/

section Producer

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

/-- **`HoldingLawInputs` at the cell-rooted law of the bridge kernel**, from `MassTransport ν` and
conullity of the gate.  No path gate and no lower bound on a time scale: the three clauses are
fixed-time definedness of the area walk and the a.s. finiteness of its holding times. -/
theorem holdingLawInputs_cellRooted (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hGc : ν Gᶜ = 0) :
    HoldingLawInputs ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot) := by
  have hprob : IsProbabilityMeasure ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot) :=
    (Measure.isProbabilityMeasure_map_iff measurable_cellRoot.aemeasurable).2 inferInstance
  have hfix : ∀ t : ℝ, ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext), ω.2.1.toFun t ≠ ⊤ := fun t =>
    ae_label_ne_top_flowKernel (hG := hG) (hwalk := hwalk) (hext := hext) ν hmt hGc t
  have hhold : ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext), ω ∈ HoldBounded :=
    ae_holdLen_ne_top_flowKernel (hG := hG) (hwalk := hwalk) (hext := hext) ν hmt hGc
  exact holdingLawInputs_of_fixed (ae_label_ne_top_map_cellRoot hfix)
    (ae_holdBounded_map_cellRoot hhold)

end Producer

/-! ## 5. The consumer join -/

/-- **`hsys` at the cell-rooted law in the singular setting, without the walk-level input.**  The
drop-in for `HoldingDataFlowSpace.scaledRootChainSystemOn_cellRooted_of_plainTransport_holding`
with `HoldingLawInputs` discharged: the only remaining input is the plain transport `hplain`
(and the gate data, which exists). -/
theorem scaledRootChainSystemOn_cellRooted_of_plainTransport_holding' {ν : Measure Env}
    [IsProbabilityMeasure ν] (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGate z G)
    (hGc : ν Gᶜ = 0)
    (hplain : CellRootedPlainTransport (ν ⊗ₘ flowKernel z G hG hwalk hext)) :
    ScaledRootChainSystemOn markedHoldGate ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot)
      DyadicGridLaw.gridMeasure gridFlow gridScaleFlow (supBlock flowHold holdGate)
      (supSel flowHold holdingData_flowSpace) :=
  scaledRootChainSystemOn_cellRooted_of_plainTransport_holding hmt hFE z G hG hwalk hext hplain
    (holdingLawInputs_cellRooted ν hmt hGc)

end ReflectedGMS.HoldingLawInputsCellRooted
