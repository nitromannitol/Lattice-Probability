/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.FlowSlotKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedTimeMTP
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SimilarityClosedGateFlow
import LatticeProb.Bonanno.ReflectedGMS.Process.ExtensionGateAllStarts

/-!
# The all-starts flow kernel and its exact similarity covariance (flow-level `law_φ`)

Packet A1 of `outputs/final-route-review.2026-09-18.md` §3.  The bridge kernel
`FlowCodingKernel.flowKernel` has only the ROOT start; the manuscript's σ-finite path measure
`ℚ_H = ∑_v a_v ℙ_H^v` (`p:eq:sigmapath`, tex:1346) needs the two-sided law from EVERY start.

* `flowSlotKernel z G hG hwalk hext n : Kernel Env FlowCoding` — at `e ∈ G` with slot `n` active,
  the image of two independent area walks from `n` under `FlowCodingKernel.build`; `δ cemFlow`
  otherwise.  Measurable in `e` through the rational-time code (`liftKernelRat`) of the raw slot
  kernel `RegenerationKernel.twoSidedSlotKernel`.  `flowKernel_apply_eq_flowSlotKernel`: the bridge
  kernel IS the root-slot member (for every extension proof `hext'` of the bridge kernel).
* `ae_build_fixed`, `ae_flowSlotKernel_fixed`: **finite-dimensional laws at arbitrary real times from
  every start** — at every fixed real time the built configuration is at a vertex `v`, its label is
  `v` and its position is `z e v`, a.s. (forward half for `t ≥ 0`; backward half read through its
  left limit for `t < 0`, which at a fixed time is the value because the walk is locally constant).
* `ae_flowSlotKernel_start` (starts at its slot) and `ae_volume_notVertex_flowSlotKernel`
  (Lebesgue-a.e. time is a vertex time, a.s.).
* **`map_simCoding_flowSlotKernel`** — the EXACT similarity covariance on a similarity-closed gate:
  `(κ_n(e)).map (simCoding s u e) = κ_{σ n}(σ e)` for every active `n` and every similarity
  `x ↦ s • (x - u)`, where `simCoding s u e` is the coding part of `reScale s ∘ reFrame u` and
  `σ = simLabel s u hs e`.  Route: two laws on the carrier agree iff their rational-time images
  agree (`ext_of_map_ratRead`); the rational-time image of the dilated configuration reads the
  original at the real times `q / s²`, where the fixed-time laws identify it with the raw two-sided
  coding; there `SimilarityClosedGateFlow.twoSidedSlotLaw_similarity_of_iff` (the raw `law_φ`) and
  the covariance of the representative field close it.  `map_simCoding_flowSlotKernel_of_relabel`:
  the same along any similarity relabelling.

Hypotheses: the gate `G` measurable and admissible, and `ExtensionGateAll z G` — the càdlàg
extension of the representative path from EVERY start at EVERY gate environment.  At
`similarityClosedGate` it is PROVED for every cell-representative rule
(`extensionGateAll_similarityClosedGate`, from
`ExtensionGateAllStarts.extensionAllStarts_of_mem_similarityClosedGate`), and §5 packages the
closed-gate kernel `closedSlotKernel z hz n` and its covariance with no remaining input.  The covariance additionally needs the gate
similarity closed and the field covariant (`RepTranslationCovariant ∧ RepDilationCovariant`, or
directly `RepSimilarityCovariant`); for `InteriorRepresentative.interiorField` at
`similarityClosedGate` both hold.  At an inactive slot the statement is false in general (the
cemetery configuration's constant position `0` moves to `-s • u`), and it is not claimed there.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.FlowSlotKernel

open Code EnvironmentFields EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationCoding ReflectedGMS.RegenerationKernel
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.FlowCodingLine
open ReflectedGMS.FlowCodingKernel ReflectedGMS.CellRootedTemporalTransport
open ReflectedGMS.CellRootedTimeMTP ReflectedGMS.AreaClockSimilarity
open ReflectedGMS.ReflectedWalkDilation ReflectedGMS.SimilarityClosedGateFlow
open ReflectedGMS.ActualMarkedBlockTransport

/-! ### 1. The all-starts extension gate and conull good sets -/

/-- **The all-starts extension input**: at every gate environment, from EVERY start, the
representative path of the area walk extends càdlàg almost surely. -/
def ExtensionGateAll (z : CellField) (G : Set Env) : Prop :=
  ∀ e ∈ G, ∀ v : Vertex e.val, ∀ᵐ ω ∂(areaFamily e).P v, ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
    ∀ t w, (areaFamily e).X t ω = some w → Z t = z.at e w

theorem ExtensionGateAll.extensionGate {z : CellField} {G : Set Env}
    (h : ExtensionGateAll z G) : ExtensionGate z G :=
  fun e hl => h e hl.1 (rootVertex hl)

/-- The good set of sample pairs is conull from every start with an a.s. extension. -/
theorem ae_mem_goodSet_of_ext {z : CellField} {e : Env} (hadm : EnvironmentAreaClockAdmissible e)
    (r : Vertex e.val)
    (hext : ∀ᵐ ω ∂(areaFamily e).P r, ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
      ∀ t v, (areaFamily e).X t ω = some v → Z t = z.at e v) :
    ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), ω ∈ goodSet z e r := by
  set P := (areaFamily e).P r with hPdef
  have hw := isReflectedWalk_areaFamily e hadm
  have hhalf : ∀ᵐ ω ∂P, HalfGood z e r ω := by
    have hfix : ∀ᵐ ω ∂P, ∀ q : ℚ, (∃ v, (areaFamily e).X (q : ℝ).toNNReal ω = some v) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball ((q : ℝ).toNNReal) ε,
          (areaFamily e).X s ω = (areaFamily e).X (q : ℝ).toNNReal ω :=
      ae_all_iff.2 fun q => (hw r).2.1 ((q : ℝ).toNNReal)
    filter_upwards [TwoSidedCycleSplice.ae_isRegLL_label e hadm r, hext, hfix, (hw r).1]
      with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hpair : ∀ᵐ ω ∂(P.prod P), HalfGood z e r ω.1 ∧ HalfGood z e r ω.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hhalf,
      Measure.quasiMeasurePreserving_snd.ae hhalf] with ω h1 h2
    exact ⟨h1, h2⟩
  have hnull : (P.prod P) (toMeasurable (P.prod P)
      {ω | ¬ (HalfGood z e r ω.1 ∧ HalfGood z e r ω.2)}) = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 hpair
  rw [ae_iff]
  have hc : {ω | ¬ ω ∈ goodSet z e r} = toMeasurable (P.prod P)
      {ω | ¬ (HalfGood z e r ω.1 ∧ HalfGood z e r ω.2)} := by
    ext ω
    simp [goodSet, hPdef]
  rw [hc]
  exact hnull

/-! ### 2. The slot fibres and the kernel -/

/-- The label trajectories of a sample pair (the raw two-sided coding). -/
noncomputable def trajPair {e : Env} (ω : (areaFamily e).Ω × (areaFamily e).Ω) : TwoSidedCoding :=
  (labelTraj ((areaFamily e).trajectory ω.1), labelTraj ((areaFamily e).trajectory ω.2))

theorem measurable_trajPair (e : Env) :
    Measurable fun ω : (areaFamily e).Ω × (areaFamily e).Ω => trajPair ω :=
  (measurable_labelTraj_trajectory.comp measurable_fst).prodMk
    (measurable_labelTraj_trajectory.comp measurable_snd)

/-- On a live slot the raw two-sided slot law is the image of the sample pair law. -/
theorem twoSidedSlotLaw_of_live {G : Set Env} {n : ℕ} {e : Env}
    (h : e ∈ G ∧ (e.val.1 n).isSome) :
    twoSidedSlotLaw G n e = (((areaFamily e).P ⟨n, h.2⟩).prod ((areaFamily e).P ⟨n, h.2⟩)).map
      trajPair := by
  set P := (areaFamily e).P ⟨n, h.2⟩ with hPdef
  have hsl : slotLaw G n e = P.map fun ω => labelTraj ((areaFamily e).trajectory ω) := by
    rw [slotLaw_of_mem h.1 h.2, ProcessFamily.law,
      Measure.map_map measurable_labelTraj (areaFamily e).measurable_trajectory]
    rfl
  show (slotLaw G n e).prod (slotLaw G n e) = _
  rw [hsl, Measure.map_prod_map _ _ measurable_labelTraj_trajectory
    measurable_labelTraj_trajectory]
  rfl

open Classical in
/-- **The fibre from slot `n`**: two independent area walks from `n`, built into the carrier, on a
live slot; the cemetery configuration otherwise. -/
noncomputable def slotFibre (z : CellField) (G : Set Env) (n : ℕ) (e : Env) : Measure FlowCoding :=
  if h : e ∈ G ∧ (e.val.1 n).isSome then
    (((areaFamily e).P ⟨n, h.2⟩).prod ((areaFamily e).P ⟨n, h.2⟩)).map (build z e ⟨n, h.2⟩)
  else Measure.dirac cemFlow

theorem slotFibre_of_live {z : CellField} {G : Set Env} {n : ℕ} {e : Env}
    (h : e ∈ G ∧ (e.val.1 n).isSome) :
    slotFibre z G n e = (((areaFamily e).P ⟨n, h.2⟩).prod ((areaFamily e).P ⟨n, h.2⟩)).map
      (build z e ⟨n, h.2⟩) := by
  classical
  unfold slotFibre
  rw [dif_pos h]

theorem slotFibre_of_not {z : CellField} {G : Set Env} {n : ℕ} {e : Env}
    (h : ¬ (e ∈ G ∧ (e.val.1 n).isSome)) : slotFibre z G n e = Measure.dirac cemFlow := by
  classical
  unfold slotFibre
  rw [dif_neg h]

/-- The rational-code kernel of the slot-`n` two-sided law. -/
noncomputable def ratSlotKernel (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (n : ℕ) : Kernel Env RatCode :=
  Kernel.map (Kernel.id ×ₖ twoSidedSlotKernel G hG hwalk
    (RegenerationKernelMeasurability.measurable_slotTransition G hG hwalk) n) (ratCode z)

theorem ratSlotKernel_apply (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (n : ℕ) (e : Env) :
    ratSlotKernel z G hG hwalk n e = (twoSidedSlotLaw G n e).map fun x => ratCode z (e, x) := by
  rw [ratSlotKernel, Kernel.map_apply _ (measurable_ratCode z), Kernel.prod_apply, Kernel.id_apply,
    twoSidedSlotKernel_apply, Measure.dirac_prod,
    Measure.map_map (measurable_ratCode z) measurable_prodMk_left]
  rfl

/-- The rational-time image of the slot fibre is the rational code of the raw slot law. -/
theorem map_ratRead_slotFibre {z : CellField} {G : Set Env} (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGateAll z G) (n : ℕ)
    (e : Env) : (slotFibre z G n e).map ratRead = ratSlotKernel z G hG hwalk n e := by
  rw [ratSlotKernel_apply]
  have hm : Measurable fun x : TwoSidedCoding => ratCode z (e, x) :=
    (measurable_ratCode z).comp measurable_prodMk_left
  by_cases h : e ∈ G ∧ (e.val.1 n).isSome
  · rw [slotFibre_of_live h, Measure.map_map measurable_ratRead (measurable_build z e _),
      twoSidedSlotLaw_of_live h, Measure.map_map hm (measurable_trajPair e)]
    refine Measure.map_congr ?_
    filter_upwards [ae_mem_goodSet_of_ext (hwalk e h.1) ⟨n, h.2⟩ (hext e h.1 ⟨n, h.2⟩)] with ω hω
    exact ratRead_build_of_mem hω
  · rw [slotFibre_of_not h, Measure.map_dirac' measurable_ratRead]
    have hlaw : twoSidedSlotLaw G n e = Measure.dirac ((cemetery, cemetery) : TwoSidedCoding) := by
      show (slotLaw G n e).prod (slotLaw G n e) = _
      rw [slotLaw_of_not h, Measure.dirac_prod_dirac]
    rw [hlaw, Measure.map_dirac' hm]
    congr 1
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
    · show (⊤ : ℕ∞) = rawLabel (cemetery, cemetery) q
      unfold rawLabel
      split_ifs <;> rfl
    · show (0 : Plane) = repAt z e (rawLabel (cemetery, cemetery) q)
      have hq : rawLabel (cemetery, cemetery) q = ⊤ := by
        unfold rawLabel
        split_ifs <;> rfl
      rw [hq, repAt_top]

/-- **The all-starts flow kernel** `e ↦ ℙ_H^{H_n}` on the carrier. -/
noncomputable def flowSlotKernel (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGateAll z G) (n : ℕ) :
    Kernel Env FlowCoding :=
  liftKernelRat (ratSlotKernel z G hG hwalk n) (slotFibre z G n)
    (map_ratRead_slotFibre hG hwalk hext n)

section Kernel

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGateAll z G}

theorem flowSlotKernel_apply (n : ℕ) (e : Env) :
    flowSlotKernel z G hG hwalk hext n e = slotFibre z G n e := rfl

instance flowSlotKernel_isMarkovKernel (n : ℕ) :
    IsMarkovKernel (flowSlotKernel z G hG hwalk hext n) := by
  refine ⟨fun e => ?_⟩
  rw [flowSlotKernel_apply]
  by_cases h : e ∈ G ∧ (e.val.1 n).isSome
  · rw [slotFibre_of_live h]
    infer_instance
  · rw [slotFibre_of_not h]
    infer_instance

/-- **The bridge kernel is the root-slot member of the all-starts kernel** (definitionally). -/
theorem flowKernel_apply_eq_flowSlotKernel (hext' : ExtensionGate z G) (e : Env) :
    flowKernel z G hG hwalk hext' e = flowSlotKernel z G hG hwalk hext (rootLabel e) e := by
  rw [flowKernel_apply, flowSlotKernel_apply]
  by_cases h : Live G e
  · rw [flowFibre_of_live h, slotFibre_of_live h]
    rfl
  · rw [flowFibre_of_not_live h, slotFibre_of_not h]

end Kernel

/-! ### 3. Finite-dimensional laws at arbitrary real times, from every start -/

/-- The raw two-sided state of a sample pair at a real time (forward half at `t ≥ 0`, backward
half at `-t`); this is `AreaClockRealTimeShift.twoSidedReal`. -/
noncomputable def sampleAt {e : Env} (ω : (areaFamily e).Ω × (areaFamily e).Ω) (t : ℝ) :
    Option (Vertex e.val) :=
  if 0 ≤ t then (areaFamily e).X t.toNNReal ω.1 else (areaFamily e).X (-t).toNNReal ω.2

/-- At a point of local constancy the extended position path is constant on a left
neighbourhood. -/
theorem extPath_eventually_const_of_fixed {z : CellField} {e : Env} {r : Vertex e.val}
    {ω : (areaFamily e).Ω} (hg : HalfGood z e r ω) {a : ℝ} {v : Vertex e.val}
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a.toNNReal ε,
      (areaFamily e).X s ω = (areaFamily e).X a.toNNReal ω)
    (hv : (areaFamily e).X a.toNNReal ω = some v) :
    ∀ᶠ x in 𝓝[<] a, extPath z e ω x.toNNReal = z.at e v := by
  obtain ⟨ε, hε, hball⟩ := h
  have hcont : ContinuousAt Real.toNNReal a := continuous_real_toNNReal.continuousAt
  have hmem : Real.toNNReal ⁻¹' Metric.ball a.toNNReal ε ∈ 𝓝 a :=
    hcont (Metric.ball_mem_nhds _ hε)
  filter_upwards [nhdsWithin_le_nhds hmem] with x hx
  exact (extPath_spec hg).2 _ v ((hball _ hx).trans hv)

/-- **The fixed-real-time law of a built configuration**: at every fixed real time, almost surely,
the raw two-sided state is a vertex `v`, the built label is `v` and the built position is `z e v`. -/
theorem ae_build_fixed {z : CellField} {e : Env} (hadm : EnvironmentAreaClockAdmissible e)
    (r : Vertex e.val)
    (hgood : ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), ω ∈ goodSet z e r)
    (t : ℝ) :
    ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), ∃ v : Vertex e.val,
      sampleAt ω t = some v ∧ (build z e r ω).1.toFun t = ((v.val : ℕ) : ℕ∞) ∧
        (build z e r ω).2.toFun t = z.value e v.val := by
  have hw := isReflectedWalk_areaFamily e hadm
  have hfix : ∀ τ : ℝ≥0, ∀ᵐ ω ∂(areaFamily e).P r,
      (∃ v, (areaFamily e).X τ ω = some v) ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ s ∈ Metric.ball τ ε, (areaFamily e).X s ω = (areaFamily e).X τ ω :=
    fun τ => (hw r).2.1 τ
  by_cases ht : 0 ≤ t
  · filter_upwards [hgood, Measure.quasiMeasurePreserving_fst.ae (hfix t.toNNReal)]
      with ω hω h1
    obtain ⟨⟨v, hv⟩, -⟩ := h1
    have hg := halfGood_of_mem_goodSet z e r hω
    refine ⟨v, ?_, ?_, ?_⟩
    · rw [sampleAt, if_pos ht]
      exact hv
    · rw [build_label_of_nonneg hω ht, hv]
      rfl
    · rw [build_of_mem z e r hω]
      show glue (fun s : ℝ => extPath z e ω.1 s.toNNReal) (fun s : ℝ => extPath z e ω.2 s.toNNReal)
        t = _
      rw [glue_of_nonneg _ _ ht, (extPath_spec hg.1).2 _ v hv]
      rfl
  · have ht' : t < 0 := not_le.1 ht
    filter_upwards [hgood, Measure.quasiMeasurePreserving_snd.ae (hfix (-t).toNNReal)]
      with ω hω h1
    obtain ⟨⟨v, hv⟩, hloc⟩ := h1
    have hg := halfGood_of_mem_goodSet z e r hω
    refine ⟨v, ?_, ?_, ?_⟩
    · rw [sampleAt, if_neg ht]
      exact hv
    · rw [build_of_mem z e r hω]
      show glue (fun s : ℝ => labelPath e ω.1 s.toNNReal)
        (fun s : ℝ => labelPath e ω.2 s.toNNReal) t = _
      rw [glue_of_neg _ _ ht',
        leftLim_eq_of_eventuallyEq_const (labelPath_eventually_const_of_fixed (a := -t) hloc)]
      show toENatLabel (((areaFamily e).X (-t).toNNReal ω.2).map Subtype.val) = _
      rw [hv]
      rfl
    · rw [build_of_mem z e r hω]
      show glue (fun s : ℝ => extPath z e ω.1 s.toNNReal) (fun s : ℝ => extPath z e ω.2 s.toNNReal)
        t = _
      rw [glue_of_neg _ _ ht',
        leftLim_eq_of_eventuallyEq_const (extPath_eventually_const_of_fixed hg.2 hloc hv)]
      rfl

section Fibre

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGateAll z G}

theorem ae_mem_goodSet_live (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hext : ExtensionGateAll z G) {e : Env} {n : ℕ} (h : e ∈ G ∧ (e.val.1 n).isSome) :
    ∀ᵐ ω ∂(((areaFamily e).P ⟨n, h.2⟩).prod ((areaFamily e).P ⟨n, h.2⟩)),
      ω ∈ goodSet z e ⟨n, h.2⟩ :=
  ae_mem_goodSet_of_ext (hwalk e h.1) ⟨n, h.2⟩ (hext e h.1 ⟨n, h.2⟩)

theorem measurableSet_fixedVertex (e : Env) (t : ℝ) :
    MeasurableSet {x : FlowCoding | ∃ v : Vertex e.val,
      x.1.toFun t = ((v.val : ℕ) : ℕ∞) ∧ x.2.toFun t = z.value e v.val} := by
  have hset : {x : FlowCoding | ∃ v : Vertex e.val,
      x.1.toFun t = ((v.val : ℕ) : ℕ∞) ∧ x.2.toFun t = z.value e v.val} =
      ⋃ v : Vertex e.val, ({x : FlowCoding | x.1.toFun t = ((v.val : ℕ) : ℕ∞)} ∩
        {x : FlowCoding | x.2.toFun t = z.value e v.val}) := by
    ext x
    simp
  rw [hset]
  refine MeasurableSet.iUnion fun v => MeasurableSet.inter ?_ ?_
  · exact ((CadlagPath.measurable_eval t).comp measurable_fst) (measurableSet_singleton _)
  · exact ((CadlagPath.measurable_eval t).comp measurable_snd) (measurableSet_singleton _)

/-- **Fixed-real-time law of the all-starts kernel**: at a live slot, at every fixed real time,
almost surely the label is a vertex `v` and the position is `z e v`. -/
theorem ae_flowSlotKernel_fixed {e : Env} {n : ℕ} (h : e ∈ G ∧ (e.val.1 n).isSome) (t : ℝ) :
    ∀ᵐ x ∂(flowSlotKernel z G hG hwalk hext n e), ∃ v : Vertex e.val,
      x.1.toFun t = ((v.val : ℕ) : ℕ∞) ∧ x.2.toFun t = z.value e v.val := by
  rw [flowSlotKernel_apply, slotFibre_of_live h]
  refine (ae_map_iff (measurable_build z e _).aemeasurable (measurableSet_fixedVertex e t)).2 ?_
  filter_upwards [ae_build_fixed (hwalk e h.1) ⟨n, h.2⟩ (ae_mem_goodSet_live hwalk hext h) t]
    with ω hω
  obtain ⟨v, -, h1, h2⟩ := hω
  exact ⟨v, h1, h2⟩

/-- **The all-starts kernel starts at its slot.** -/
theorem ae_flowSlotKernel_start {e : Env} {n : ℕ} (h : e ∈ G ∧ (e.val.1 n).isSome) :
    ∀ᵐ x ∂(flowSlotKernel z G hG hwalk hext n e), x.1.toFun 0 = (n : ℕ∞) := by
  rw [flowSlotKernel_apply, slotFibre_of_live h]
  have hS : MeasurableSet {x : FlowCoding | x.1.toFun 0 = (n : ℕ∞)} :=
    ((CadlagPath.measurable_eval 0).comp measurable_fst) (measurableSet_singleton _)
  refine (ae_map_iff (measurable_build z e _).aemeasurable hS).2 ?_
  filter_upwards [ae_mem_goodSet_live hwalk hext h] with ω hω
  exact build_label_zero hω

/-- **Lebesgue-a.e. time is a vertex time**, almost surely under the all-starts kernel at a live
slot (fixed-time definedness plus Tonelli). -/
theorem ae_volume_notVertex_flowSlotKernel {e : Env} {n : ℕ} (h : e ∈ G ∧ (e.val.1 n).isSome) :
    ∀ᵐ x ∂(flowSlotKernel z G hG hwalk hext n e),
      volume {t : ℝ | ∀ m : Vertex e.val, x.1.toFun t ≠ ((m.val : ℕ) : ℕ∞)} = 0 := by
  have hS : MeasurableSet {p : FlowCoding × ℝ | ∃ m : Vertex e.val,
      p.1.1.toFun p.2 = ((m.val : ℕ) : ℕ∞)} := by
    have hset : {p : FlowCoding × ℝ | ∃ m : Vertex e.val, p.1.1.toFun p.2 = ((m.val : ℕ) : ℕ∞)} =
        ⋃ m : Vertex e.val, {p : FlowCoding × ℝ | p.1.1.toFun p.2 = ((m.val : ℕ) : ℕ∞)} := by
      ext p
      simp
    rw [hset]
    exact MeasurableSet.iUnion fun m => ((CadlagPath.measurable_eval_uncurry).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) (measurableSet_singleton _)
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂(flowSlotKernel z G hG hwalk hext n e),
      ∃ m : Vertex e.val, x.1.toFun t = ((m.val : ℕ) : ℕ∞) :=
    Filter.Eventually.of_forall fun t => (ae_flowSlotKernel_fixed h t).mono
      fun x hx => let ⟨v, hv, _⟩ := hx; ⟨v, hv⟩
  have h' := (Measure.ae_ae_comm (p := fun (x : FlowCoding) (t : ℝ) =>
    ∃ m : Vertex e.val, x.1.toFun t = ((m.val : ℕ) : ℕ∞)) hS).2 hall
  filter_upwards [h'] with x hx
  rw [ae_iff] at hx
  simpa only [not_exists] using hx

end Fibre

/-! ### 4. The exact similarity covariance (flow-level `law_φ`) -/

/-- Two laws on the carrier with the same rational-time image are equal. -/
theorem ext_of_map_ratRead {μ ν : Measure FlowCoding} (h : μ.map ratRead = ν.map ratRead) :
    μ = ν := by
  ext s hs
  obtain ⟨B, hB, rfl⟩ := exists_ratRead_preimage hs
  rw [← Measure.map_apply measurable_ratRead hB, h, Measure.map_apply measurable_ratRead hB]

theorem toENatLabel_map (f : ℕ → ℕ) (o : Option ℕ) :
    toENatLabel (o.map f) = liftLabel f (toENatLabel o) := by
  cases o with
  | none => exact (liftLabel_top f).symm
  | some n => exact (liftLabel_natCast f n).symm

theorem parabolicFactor_inv_mul_toNNReal {s : ℝ} {q : ℝ} (hq : 0 ≤ q) :
    (parabolicFactor s)⁻¹ * q.toNNReal = ((s ^ 2)⁻¹ * q).toNNReal := by
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_inv, coe_parabolicFactor, Real.coe_toNNReal _ hq,
    Real.coe_toNNReal _ (mul_nonneg (inv_nonneg.2 (sq_nonneg s)) hq)]

/-- **The raw two-sided coding after the parabolic dilation, read at a rational time**, is the
relabelled raw state at the real time `q / s²`. -/
theorem rawLabel_dilate_trajPair {e : Env} (σ : ℕ → ℕ) {s : ℝ} (hs : 0 < s)
    (ω : (areaFamily e).Ω × (areaFamily e).Ω) (q : ℚ) :
    rawLabel (Prod.map (dilateTraj σ (parabolicFactor s)) (dilateTraj σ (parabolicFactor s))
        (trajPair ω)) q =
      liftLabel σ (toENatLabel ((sampleAt ω ((s ^ 2)⁻¹ * (q : ℝ))).map Subtype.val)) := by
  have hs2 : (0 : ℝ) < (s ^ 2)⁻¹ := inv_pos.2 (pow_pos hs 2)
  unfold rawLabel sampleAt
  by_cases hq : 0 ≤ q
  · have hq' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hτ : 0 ≤ (s ^ 2)⁻¹ * (q : ℝ) := mul_nonneg hs2.le hq'
    rw [if_pos hq, if_pos hτ]
    show toENatLabel ((((areaFamily e).X ((parabolicFactor s)⁻¹ * (q : ℝ).toNNReal) ω.1).map
      Subtype.val).map σ) = _
    rw [parabolicFactor_inv_mul_toNNReal hq', toENatLabel_map]
  · have hq' : (q : ℝ) < 0 := by exact_mod_cast not_le.1 hq
    have hτ : ¬ 0 ≤ (s ^ 2)⁻¹ * (q : ℝ) := not_le.2 (mul_neg_of_pos_of_neg hs2 hq')
    rw [if_neg hq, if_neg hτ]
    show toENatLabel ((((areaFamily e).X ((parabolicFactor s)⁻¹ * (-(q : ℝ)).toNNReal) ω.2).map
      Subtype.val).map σ) = _
    rw [parabolicFactor_inv_mul_toNNReal (neg_nonneg.2 hq'.le), toENatLabel_map, mul_neg]

/-- **Similarity covariance of a representative field** along the canonical label map, in the
form used here: `z (σ e) (σ n) = s • (z e n - u)`. -/
def RepSimilarityCovariant (rep : Env → ℕ → Plane) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) (n : ℕ), (e.val.1 n).isSome →
    rep (similarityTargetEnv s u hs e) (simLabel s u hs e n) = s • (rep e n - u)

/-- Translation and dilation covariance give the full similarity covariance. -/
theorem repSimilarityCovariant_of_covariant {rep : Env → ℕ → Plane}
    (hT : RepTranslationCovariant rep) (hD : RepDilationCovariant rep) :
    RepSimilarityCovariant rep := by
  intro s u hs e n hn
  have h1 : similarityTargetEnv s u hs e = similarityTargetEnv s 0 hs (translateEnv u e) := by
    show _ = similarityTargetEnv s 0 hs (similarityTargetEnv 1 u one_pos e)
    rw [MarkedSimilarityActionLaws.similarityTargetEnv_similarityTargetEnv]
    exact similarityTargetEnv_congr _ _ (mul_one s).symm (by simp) _
  have h2 : simLabel s u hs e n = simLabel s 0 hs (translateEnv u e) (simLabel 1 u one_pos e n) :=
    (simLabel_reScale_reFrame hs u e n).symm
  have hn' : ((translateEnv u e).val.1 (simLabel 1 u one_pos e n)).isSome := isSome_simLabel hn
  rw [h2, h1, hD s hs _ _ hn', hT u e n hn]

/-- **The exact similarity covariance of the slot fibres** (flow-level `law_φ`): on a live slot of
a gate that contains the image environment, the similarity action on the coding carries the
fibre from `n` onto the fibre from `σ n` in the image environment. -/
theorem map_simCoding_slotFibre {z : CellField} {G : Set Env} (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGateAll z G)
    (hz : RepSimilarityCovariant z.value) {s : ℝ} (hs : 0 < s) (u : Plane) {e : Env}
    (he : e ∈ G) (he' : similarityTargetEnv s u hs e ∈ G) {n : ℕ} (hn : (e.val.1 n).isSome) :
    (slotFibre z G n e).map (simCoding s u e) =
      slotFibre z G (simLabel s u hs e n) (similarityTargetEnv s u hs e) := by
  refine ext_of_map_ratRead ?_
  rw [map_ratRead_slotFibre hG hwalk hext, ratSlotKernel_apply]
  have hrel := LabelBijectionProducer.isSimilarityRelabel_similarityRelabel s u hs e
  have hlab : ∀ v : Vertex e.val,
      simLabel s u hs e v.val = (LabelBijectionProducer.similarityRelabel s u hs e v).val :=
    fun v => simLabel_of_isSome v.property
  have hraw := twoSidedSlotLaw_similarity_of_iff hwalk hrel ⟨fun _ => he', fun _ => he⟩
    (simLabel s u hs e) hlab ⟨n, hn⟩
  rw [← hlab ⟨n, hn⟩] at hraw
  have hdil : Measurable (Prod.map (dilateTraj (simLabel s u hs e) (parabolicFactor s))
      (dilateTraj (simLabel s u hs e) (parabolicFactor s))) :=
    (measurable_dilateTraj _ _).prodMap (measurable_dilateTraj _ _)
  have hm' : Measurable fun x : TwoSidedCoding => ratCode z (similarityTargetEnv s u hs e, x) :=
    (measurable_ratCode z).comp measurable_prodMk_left
  rw [hraw, Measure.map_map hm' hdil, twoSidedSlotLaw_of_live ⟨he, hn⟩,
    Measure.map_map (hm'.comp hdil) (measurable_trajPair e),
    Measure.map_map measurable_ratRead (measurable_simCoding hs u e), slotFibre_of_live ⟨he, hn⟩,
    Measure.map_map (measurable_ratRead.comp (measurable_simCoding hs u e)) (measurable_build z e _)]
  refine Measure.map_congr ?_
  have hfix := ae_all_iff.2 fun q : ℚ => ae_build_fixed (z := z) (hwalk e he) ⟨n, hn⟩
    (ae_mem_goodSet_live hwalk hext ⟨he, hn⟩) ((s ^ 2)⁻¹ * (q : ℝ))
  filter_upwards [hfix] with ω hω
  refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
  · obtain ⟨v, hsv, hl, -⟩ := hω q
    show (simCoding s u e (build z e ⟨n, hn⟩ ω)).1.toFun (q : ℝ) =
      rawLabel (Prod.map (dilateTraj (simLabel s u hs e) (parabolicFactor s))
        (dilateTraj (simLabel s u hs e) (parabolicFactor s)) (trajPair ω)) q
    rw [simCoding_label hs, hl, rawLabel_dilate_trajPair _ hs, hsv]
    rfl
  · obtain ⟨v, hsv, hl, hp⟩ := hω q
    show (simCoding s u e (build z e ⟨n, hn⟩ ω)).2.toFun (q : ℝ) =
      repAt z (similarityTargetEnv s u hs e)
        (rawLabel (Prod.map (dilateTraj (simLabel s u hs e) (parabolicFactor s))
          (dilateTraj (simLabel s u hs e) (parabolicFactor s)) (trajPair ω)) q)
    rw [simCoding_pos hs, hp, rawLabel_dilate_trajPair _ hs, hsv]
    show s • (z.value e v.val - u) =
      repAt z (similarityTargetEnv s u hs e) (liftLabel (simLabel s u hs e) (v.val : ℕ∞))
    rw [liftLabel_natCast, repAt_natCast, hz s u hs e v.val v.property]

/-- **The exact similarity covariance of the all-starts kernel**, at every active slot of every
environment of a similarity-closed gate. -/
theorem map_simCoding_flowSlotKernel {z : CellField} {G : Set Env} (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGateAll z G)
    (hGsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env),
      e ∈ G ↔ similarityTargetEnv s u hs e ∈ G)
    (hz : RepSimilarityCovariant z.value) {s : ℝ} (hs : 0 < s) (u : Plane) {e : Env}
    (he : e ∈ G) {n : ℕ} (hn : (e.val.1 n).isSome) :
    (flowSlotKernel z G hG hwalk hext n e).map (simCoding s u e) =
      flowSlotKernel z G hG hwalk hext (simLabel s u hs e n) (similarityTargetEnv s u hs e) :=
  map_simCoding_slotFibre hG hwalk hext hz hs u he ((hGsim s u hs e).1 he) hn

/-! ### 5. At the similarity-closed gate: no remaining input -/

open ReflectedGMS.SimilarityClosedGate

/-- **The all-starts extension at the similarity-closed gate**, for every cell-representative
rule (`ExtensionGateAllStarts.extensionAllStarts_of_mem_similarityClosedGate`). -/
theorem extensionGateAll_similarityClosedGate (z : CellField) (hz : IsCellRepresentative z) :
    ExtensionGateAll z similarityClosedGate :=
  fun _ he => ExtensionGateAllStarts.extensionAllStarts_of_mem_similarityClosedGate z hz he

/-- The similarity-closed gate is closed under the canonical similarity action. -/
theorem mem_similarityClosedGate_iff_target (s : ℝ) (u : Plane) (hs : 0 < s) (e : Env) :
    e ∈ similarityClosedGate ↔ similarityTargetEnv s u hs e ∈ similarityClosedGate :=
  mem_similarityClosedGate_iff_of_isSimilarity (isSimilarity_similarityTargetEnv s u hs e)

/-- **The all-starts kernel at the similarity-closed gate**, with no remaining input. -/
noncomputable def closedSlotKernel (z : CellField) (hz : IsCellRepresentative z) (n : ℕ) :
    Kernel Env FlowCoding :=
  flowSlotKernel z similarityClosedGate measurableSet_similarityClosedGate
    (fun _ he => environmentAreaClockAdmissible_of_mem he)
    (extensionGateAll_similarityClosedGate z hz) n

instance closedSlotKernel_isMarkovKernel (z : CellField) (hz : IsCellRepresentative z) (n : ℕ) :
    IsMarkovKernel (closedSlotKernel z hz n) := by
  unfold closedSlotKernel
  infer_instance

/-- **The exact similarity covariance at the closed gate**: every gate environment, every active
slot, every similarity. -/
theorem map_simCoding_closedSlotKernel (z : CellField) (hz : IsCellRepresentative z)
    (hzcov : RepSimilarityCovariant z.value) {s : ℝ} (hs : 0 < s) (u : Plane) {e : Env}
    (he : e ∈ similarityClosedGate) {n : ℕ} (hn : (e.val.1 n).isSome) :
    (closedSlotKernel z hz n e).map (simCoding s u e) =
      closedSlotKernel z hz (simLabel s u hs e n) (similarityTargetEnv s u hs e) :=
  map_simCoding_flowSlotKernel measurableSet_similarityClosedGate _ _
    mem_similarityClosedGate_iff_target hzcov hs u he hn

/-- The interior representative is similarity covariant in the form used here. -/
theorem repSimilarityCovariant_interiorField :
    RepSimilarityCovariant InteriorRepresentative.interiorField.value :=
  repSimilarityCovariant_of_covariant InteriorRepresentative.repTranslationCovariant_interiorField
    InteriorRepresentative.repDilationCovariant_interiorField

end ReflectedGMS.FlowSlotKernel
