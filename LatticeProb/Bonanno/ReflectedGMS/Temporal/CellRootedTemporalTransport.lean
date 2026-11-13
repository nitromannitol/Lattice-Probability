/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CellRootedTemporalTransport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CellRootedEncodingRepair
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowSpaceTimeScale

/-!
# The unmarked transport at the cell-rooted law: exact reduction and the target convention

Packet P2 of `outputs/rooting-decision-handoff.2026-09-18.md`.  Target:
`ParabolicTemporalTransport ((ν ⊗ₘ κF).map cellRoot) reRootFlow reScale`.

Checked here:

* `cellRoot_reFrame`: the cell-rooted encoding forgets the frame, `cellRoot ∘ reFrame u = cellRoot`.
* **`parabolicTemporalTransport_map_cellRoot_iff`**: for every s-finite law `P` on the carrier,
  the transport field at the cell-rooted law `P.map cellRoot` (for the re-rooting flow) is
  EQUIVALENT to `CellRootedPlainTransport P`: the same degree `-2` identity at `P` for the PLAIN
  time shift, restricted to FRAME-INVARIANT kernels.  This is the exact content of the pull-back
  through `reRootFlow_cellRoot`/`reScale_cellRoot`; no information is lost in either direction.
* `ae_label_ne_top_flowKernel`, **`ae_volume_labelTop_flowKernel`**: at `ν ⊗ₘ κF` the label path is
  at a vertex at every fixed time a.s. (fixed-time definedness of the area walk, both halves), hence
  a.s. its `⊤`-times are Lebesgue-null (Tonelli).
* `truncTarget` and its invariances (`timeShiftCovariant_truncTarget`,
  `frameInvariant_truncTarget`, `parabolicCovariant_truncTarget`), with
  `ae_lintegral_truncTarget_outgoing`/`_incoming`: the target convention (`V = 0` at nonvertex
  target times) costs nothing at `ν ⊗ₘ κF`.

NOT proved: `CellRootedPlainTransport (ν ⊗ₘ κF)` itself.  See
`outputs/cell-rooted-temporal-transport-handoff.2026-09-18.md`: the brief's target is false as
stated for a representative field that is not similarity covariant (argued counterexample), and
the weld `AreaClockTimeMTPWeld.lintegral_timeMTP_of_codedAreaClockLaw` does not apply to the
bridge kernel as it stands (it needs a `MarkedPathProcess` — `similarityCoding` at every physical
similarity, countable alphabet, laws from every start — none of which exists for `κF`).
Nothing here certifies `hsys`, `p:lem:timeMTP` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.CellRootedTemporalTransport

open Code EnvironmentFields EnvironmentLaws RootDensities
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TemporalMassTransport ReflectedGMS.ParabolicTransport
open ReflectedGMS.FlowCodingLine ReflectedGMS.FlowCodingKernel ReflectedGMS.FlowCodingFrontier
open ReflectedGMS.CellRootedEncodingRepair

/-! ### 1. The cell-rooted encoding forgets the frame -/

/-- **Frame invariance of the cell-rooted encoding.** -/
theorem cellRoot_reFrame (u : Plane) (ω : FlowSpace) : cellRoot (reFrame u ω) = cellRoot ω := by
  rw [cellRoot_eq_reFrame, cellRoot_eq_reFrame, reFrame_reFrame]
  congr 1
  show u + (ω.2.2.toFun 0 - u) = ω.2.2.toFun 0
  abel

/-- A two-time kernel on the carrier that does not see the spatial frame. -/
def FrameInvariant (V : FlowSpace → ℝ → ℝ → ℝ≥0∞) : Prop :=
  ∀ (u : Plane) (ω : FlowSpace) (s t : ℝ), V (reFrame u ω) s t = V ω s t

/-- **The plain transport for frame-invariant kernels at a law `P`**: the degree `-2` temporal
transport for the environment-fixing time shift `plainShift`, restricted to kernels that do not
see the spatial frame. -/
def CellRootedPlainTransport (P : Measure FlowSpace) : Prop :=
  ∀ V : FlowSpace → ℝ → ℝ → ℝ≥0∞, Measurable (fun p : FlowSpace × ℝ × ℝ => V p.1 p.2.1 p.2.2) →
    TimeShiftCovariant plainShift V → FrameInvariant V → ParabolicCovariant reScale V →
    ∫⁻ p : FlowSpace × ℝ, V p.1 0 p.2 ∂(P.prod volume) =
      ∫⁻ p : FlowSpace × ℝ, V p.1 p.2 0 ∂(P.prod volume)

/-- Integrals against `(P.map cellRoot) × Lebesgue` pulled back to `P × Lebesgue`. -/
theorem lintegral_prod_map_cellRoot (P : Measure FlowSpace) [SFinite P]
    (f : FlowSpace × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, f p ∂((P.map cellRoot).prod volume) =
      ∫⁻ p, f (cellRoot p.1, p.2) ∂(P.prod volume) := by
  have h : (P.map cellRoot).prod (volume : Measure ℝ) =
      (P.prod volume).map (Prod.map cellRoot id) := by
    have h1 := Measure.map_prod_map P (volume : Measure ℝ) measurable_cellRoot measurable_id
    rwa [Measure.map_id] at h1
  rw [h, lintegral_map hf (measurable_cellRoot.prodMap measurable_id)]
  rfl

/-- **The exact pull-back of the transport field through the cell-rooted encoding.**  At the
cell-rooted law `P.map cellRoot`, the degree `-2` transport for the re-rooting flow holds iff the
degree `-2` transport for the PLAIN time shift holds at `P` for every frame-invariant kernel. -/
theorem parabolicTemporalTransport_map_cellRoot_iff (P : Measure FlowSpace) [SFinite P] :
    ParabolicTemporalTransport (P.map cellRoot) reRootFlow reScale ↔
      CellRootedPlainTransport P := by
  constructor
  · intro htr V hV hcov hfr hpar
    have hcov' : TimeShiftCovariant reRootFlow V := by
      intro r s t ω
      rw [reRootFlow_eq_reFrame, hfr]
      exact hcov r s t ω
    have h := htr V hV hcov' hpar
    rw [lintegral_prod_map_cellRoot P _ (measurable_outgoing V hV),
      lintegral_prod_map_cellRoot P _ (measurable_incoming V hV)] at h
    have hfr' : ∀ (u : Plane) (ω : FlowSpace) (s t : ℝ), V (reFrame u ω) s t = V ω s t := hfr
    simpa only [cellRoot_eq_reFrame, hfr'] using h
  · intro hpl W hW hcov hpar
    have hV : Measurable fun p : FlowSpace × ℝ × ℝ => W (cellRoot p.1) p.2.1 p.2.2 :=
      hW.comp ((measurable_cellRoot.comp measurable_fst).prodMk measurable_snd)
    have hcovV : TimeShiftCovariant plainShift fun ω s t => W (cellRoot ω) s t := by
      intro r s t ω
      show W (cellRoot (plainShift r ω)) (s - r) (t - r) = W (cellRoot ω) s t
      rw [← reRootFlow_cellRoot]
      exact hcov r s t (cellRoot ω)
    have hfrV : FrameInvariant fun ω s t => W (cellRoot ω) s t := by
      intro u ω s t
      show W (cellRoot (reFrame u ω)) s t = W (cellRoot ω) s t
      rw [cellRoot_reFrame]
    have hparV : ParabolicCovariant reScale fun ω s t => W (cellRoot ω) s t := by
      intro C hC ω s t
      show W (cellRoot (reScale C ω)) (C ^ 2 * s) (C ^ 2 * t) =
        ENNReal.ofReal ((C ^ 2)⁻¹) * W (cellRoot ω) s t
      rw [← reScale_cellRoot hC]
      exact hpar C hC (cellRoot ω) s t
    have h := hpl _ hV hcovV hfrV hparV
    rw [lintegral_prod_map_cellRoot P _ (measurable_outgoing W hW),
      lintegral_prod_map_cellRoot P _ (measurable_incoming W hW)]
    exact h

/-! ### 2. Fixed-time definedness at the bridge kernel and Lebesgue-nullity of `⊤`-times -/

/-- Local constancy of the walk at a fixed (nonnegative) time makes its label path constant on a
left neighbourhood. -/
theorem labelPath_eventually_const_of_fixed {e : Env} {ω : (areaFamily e).Ω} {a : ℝ}
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a.toNNReal ε,
      (areaFamily e).X s ω = (areaFamily e).X a.toNNReal ω) :
    ∀ᶠ x in 𝓝[<] a, labelPath e ω x.toNNReal = labelPath e ω a.toNNReal := by
  obtain ⟨ε, hε, hball⟩ := h
  have hcont : ContinuousAt Real.toNNReal a := continuous_real_toNNReal.continuousAt
  have hmem : Real.toNNReal ⁻¹' Metric.ball a.toNNReal ε ∈ 𝓝 a :=
    hcont (Metric.ball_mem_nhds _ hε)
  filter_upwards [nhdsWithin_le_nhds hmem] with x hx
  have hX : (areaFamily e).X x.toNNReal ω = (areaFamily e).X a.toNNReal ω := hball _ hx
  show toENatLabel (((areaFamily e).X x.toNNReal ω).map Subtype.val) =
    toENatLabel (((areaFamily e).X a.toNNReal ω).map Subtype.val)
  rw [hX]

/-- **Fixed-time definedness of the built configuration**: at an admissible environment, at every
fixed real time the glued label path is at a vertex almost surely (forward half for `t ≥ 0`,
backward half read through its left limit for `t < 0`). -/
theorem ae_build_label_ne_top {z : CellField} {e : Env}
    (hadm : EnvironmentAreaClockAdmissible e) (r : Vertex e.val)
    (hgood : ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), ω ∈ goodSet z e r)
    (t : ℝ) :
    ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), (build z e r ω).1.toFun t ≠ ⊤ := by
  have hw := isReflectedWalk_areaFamily e hadm
  have hfix : ∀ τ : ℝ≥0, ∀ᵐ ω ∂(areaFamily e).P r,
      (∃ v, (areaFamily e).X τ ω = some v) ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ s ∈ Metric.ball τ ε, (areaFamily e).X s ω = (areaFamily e).X τ ω :=
    fun τ => (hw r).2.1 τ
  by_cases ht : 0 ≤ t
  · filter_upwards [hgood, Measure.quasiMeasurePreserving_fst.ae (hfix t.toNNReal)]
      with ω hω h1
    rw [build_of_mem z e r hω]
    show glue (fun s : ℝ => labelPath e ω.1 s.toNNReal) (fun s : ℝ => labelPath e ω.2 s.toNNReal)
      t ≠ ⊤
    rw [glue_of_nonneg _ _ ht]
    obtain ⟨⟨v, hv⟩, -⟩ := h1
    show toENatLabel (((areaFamily e).X t.toNNReal ω.1).map Subtype.val) ≠ ⊤
    rw [hv]
    simp [toENatLabel]
  · have ht' : t < 0 := not_le.1 ht
    filter_upwards [hgood, Measure.quasiMeasurePreserving_snd.ae (hfix (-t).toNNReal)]
      with ω hω h1
    rw [build_of_mem z e r hω]
    show glue (fun s : ℝ => labelPath e ω.1 s.toNNReal) (fun s : ℝ => labelPath e ω.2 s.toNNReal)
      t ≠ ⊤
    rw [glue_of_neg _ _ ht']
    obtain ⟨⟨v, hv⟩, hloc⟩ := h1
    rw [leftLim_eq_of_eventuallyEq_const (labelPath_eventually_const_of_fixed (a := -t) hloc)]
    show toENatLabel (((areaFamily e).X (-t).toNNReal ω.2).map Subtype.val) ≠ ⊤
    rw [hv]
    simp [toENatLabel]

section Kernel

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

theorem measurableSet_label_ne_top (t : ℝ) :
    MeasurableSet {ω : FlowSpace | ω.2.1.toFun t ≠ ⊤} :=
  ((CadlagPath.measurable_eval t).comp (measurable_fst.comp measurable_snd))
    (measurableSet_singleton ⊤).compl

/-- **At every fixed time the label path of `ν ⊗ₘ κF` is at a vertex almost surely.** -/
theorem ae_label_ne_top_flowKernel (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hGc : ν Gᶜ = 0) (t : ℝ) :
    ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext), ω.2.1.toFun t ≠ ⊤ := by
  have hS := measurableSet_label_ne_top t
  refine Measure.ae_compProd_of_ae_ae hS ?_
  have hGae : ∀ᵐ e ∂ν, e ∈ G := ae_iff.2 hGc
  filter_upwards [hGae, Spatial.ae_notMem_boundaryMask_of_massTransport ν hmt] with e he hm
  obtain ⟨root, hroot, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e)
    (decode_geometry e) hm
  have hlive : Live G e := ⟨he, by rw [rootLabel_of_some hroot]; exact root.property⟩
  have hSe : MeasurableSet {y : FlowCoding | ((e, y) : FlowSpace) ∈
      {ω : FlowSpace | ω.2.1.toFun t ≠ ⊤}} := measurable_prodMk_left hS
  rw [flowKernel_apply, flowFibre_of_live hlive]
  refine (ae_map_iff (measurable_build z e _).aemeasurable hSe).2 ?_
  exact ae_build_label_ne_top (hwalk e he) _ (ae_mem_goodSet hwalk hext hlive) t

/-- **The `⊤`-times of `ν ⊗ₘ κF` are almost surely Lebesgue-null** (fixed-time definedness plus
Tonelli). -/
theorem ae_volume_labelTop_flowKernel (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hGc : ν Gᶜ = 0) :
    ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext), volume {t : ℝ | ω.2.1.toFun t = ⊤} = 0 := by
  have hS : MeasurableSet {p : FlowSpace × ℝ | p.1.2.1.toFun p.2 ≠ ⊤} :=
    ((CadlagPath.measurable_eval_uncurry).comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
      (measurableSet_singleton ⊤).compl
  have h : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ ω ∂(ν ⊗ₘ flowKernel z G hG hwalk hext),
      ω.2.1.toFun t ≠ ⊤ :=
    Filter.Eventually.of_forall fun t => ae_label_ne_top_flowKernel ν hmt hGc t
  have h' := (Measure.ae_ae_comm (p := fun (ω : FlowSpace) (t : ℝ) => ω.2.1.toFun t ≠ ⊤)
    hS).2 h
  filter_upwards [h'] with ω hω
  rw [ae_iff] at hω
  simpa only [ne_eq, not_not] using hω

end Kernel

/-! ### 3. The target convention by truncation -/

section Kernel

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G}

end Kernel

/-! ### 4. The gated root-chain system at the cell-rooted law from the plain transport -/

section System

open ReflectedGMS.SimilarityClosedGate ReflectedGMS.SimilarityClosedGateFlow
open ReflectedGMS.FlowSpaceBlockSystem ReflectedGMS.FlowGateRootChainGate
open ReflectedGMS.ScaledRootChainGated ReflectedGMS.ScaledRootChain
open ReflectedGMS.TwoSidedRegenerationFlowGrid ReflectedGMS.FlowSpaceTimeScale
open HarmonicLawIngredients

/-! The gated root-chain system at the cell-rooted law is no longer assembled here.  It used
`FlowSpaceTimeScale.scaledRootChainSystemOn_flowTimeScale`, whose block criterion asks a positive
lower bound on the spatial scale at **every** time of a block — an infimum condition that is false
once cells may fail to cover a point, since the walker can sit where the scale vanishes.

The manuscript's own construction (§17) is a **supremum** of holding-interval lengths required to be
finite, with blocks defined for almost every time.  That is
`Temporal/HoldingDataFlowSpace.scaledRootChainSystemOn_cellRooted_of_plainTransport_holding`, whose
extra input `HoldingLawInputs` is discharged by
`Temporal/HoldingLawInputsCellRooted.holdingLawInputs_cellRooted`. -/

end System

end ReflectedGMS.CellRootedTemporalTransport
