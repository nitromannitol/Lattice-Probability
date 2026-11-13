/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.FlowSlotShift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowSlotKernel
import LatticeProb.Bonanno.ReflectedGMS.Temporal.AreaClockCodingShift

/-!
# Two-sided real-time shift invariance of `ℚ_H = ∑_v a_v ℙ_H^v` on the flow carrier

Packet A2 of `outputs/final-route-review.2026-09-18.md` §3.  The manuscript (tex:1346-1350):

> The sigma-finite path measure `ℚ_H = ∑_{v∈H} a_v ℙ_H^v` is invariant under every deterministic
> time shift.  This follows directly from the Markov cylinder distributions and
> `a_v p_t(v,u) = a_u p_t(u,v)`; no finite total speed mass is required.

Here `ℙ_H^v` is the all-starts flow kernel `FlowSlotKernel.flowSlotKernel … v` on the carrier
`FlowCoding = CadlagPath ℕ∞ × CadlagPath Plane` and `ℚ_H = CellRootedTimeMTP.startMixture`.

**`measurePreserving_codingShift_startMixture`**: at every gate environment and every real `r`,
the coding shift preserves `ℚ_H`.  Route (a π-system lift of `Process/AreaClockRealTimeShift`):
1. the label marginals have the finite-dimensional laws of the coded two-sided area walk at
   arbitrary real times (`codedTwoSidedLaw_labelLaw`, from `FlowSlotKernel.ae_build_fixed`), so
   their area mixture is shift invariant on `CadlagPath ℕ∞`
   (`AreaClockCodingShift.isShiftInvariantMixture_cellArea`: point cylinders, detailed balance
   `Forms/AreaTransitionReversibility`, no summability);
2. at every fixed real time the position is `z e (label)` almost surely under `ℚ_H`
   (`ae_startMixture_coupled`), so on countably many times the rational-time reading of a
   configuration — shifted or not — is the image of its labels under the measurable map
   `graphCode z e`;
3. a law on the carrier is determined by its rational-time reading
   (`FlowSlotKernel.ext_of_map_ratRead`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace ReflectedGMS.FlowSlotShift

open Code EnvironmentFields EnvironmentLaws AreaClocks
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationCoding ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.FlowCodingLine ReflectedGMS.FlowCodingKernel ReflectedGMS.CellRootedTimeMTP
open ReflectedGMS.FlowSlotKernel ReflectedGMS.AreaClockRealTimeShift
open ReflectedGMS.AreaClockCodingShift ReflectedGMS.FixedEnvironmentTemporalTransport

attribute [local instance] nontrivial_vertex

/-! ### 1. The coded label laws -/

/-- The coding of the vertex states in `ℕ∞` (nonvertex states collapsed to `⊤`). -/
def vertexCode (e : Env) (o : Option (Vertex e.val)) : ℕ∞ := toENatLabel (o.map Subtype.val)

theorem toENatLabel_injective : Function.Injective toENatLabel := fun a b h => by
  have h' := congrArg toOptLabel h
  rwa [toOptLabel_toENatLabel, toOptLabel_toENatLabel] at h'

theorem vertexCode_injective (e : Env) : Function.Injective (vertexCode e) :=
  toENatLabel_injective.comp (Option.map_injective Subtype.val_injective)

/-- The label marginal of the all-starts kernel from a vertex. -/
noncomputable def labelLaw (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGateAll z G) (e : Env)
    (v : Vertex e.val) : Measure (CadlagPath ℕ∞) :=
  (flowSlotKernel z G hG hwalk hext v.val e).map Prod.fst

section Gate

variable {z : CellField} {G : Set Env} {hG : MeasurableSet G}
  {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGateAll z G}

/-- **The label marginals have the two-sided finite-dimensional laws at arbitrary real times.** -/
theorem codedTwoSidedLaw_labelLaw {e : Env} (he : e ∈ G) :
    CodedTwoSidedLaw (areaFamily e) (vertexCode e) (labelLaw z G hG hwalk hext e) := by
  intro v J τ s
  have hlive : e ∈ G ∧ (e.val.1 v.val).isSome := ⟨he, v.property⟩
  have hbm : Measurable fun ω : (areaFamily e).Ω × (areaFamily e).Ω => (build z e v ω).1 :=
    measurable_fst.comp (measurable_build z e v)
  have hset := measurableSet_pathCyl (S := ℕ∞) J τ s
  have hlaw : labelLaw z G hG hwalk hext e v =
      (((areaFamily e).P v).prod ((areaFamily e).P v)).map fun ω => (build z e v ω).1 := by
    rw [labelLaw, flowSlotKernel_apply, slotFibre_of_live hlive,
      Measure.map_map measurable_fst (measurable_build z e _)]
    rfl
  rw [hlaw, Measure.map_apply hbm hset]
  show _ = (((areaFamily e).P v).prod ((areaFamily e).P v))
    (codedCyl (areaFamily e) (vertexCode e) J τ s)
  refine measure_congr ?_
  have hall : ∀ᵐ ω ∂(((areaFamily e).P v).prod ((areaFamily e).P v)), ∀ q ∈ J,
      ∃ w : Vertex e.val, sampleAt ω (τ q) = some w ∧
        (build z e v ω).1.toFun (τ q) = ((w.val : ℕ) : ℕ∞) ∧
          (build z e v ω).2.toFun (τ q) = z.value e w.val :=
    (Filter.eventually_all_finset J).2 fun q _ =>
      ae_build_fixed (hwalk e he) v (ae_mem_goodSet_live hwalk hext hlive) (τ q)
  filter_upwards [hall] with ω hω
  simp only [codedCyl, mem_preimage, mem_setOf_eq, eq_iff_iff]
  refine forall₂_congr fun q hq => ?_
  obtain ⟨w, hs, hl, -⟩ := hω q hq
  have htw : twoSidedReal (areaFamily e) ω (τ q) = some w := hs
  rw [hl, htw]
  exact Iff.rfl

/-- **Real-time shift invariance of the area mixture of the label marginals.** -/
theorem isShiftInvariantMixture_labelLaw {e : Env} (he : e ∈ G) :
    IsShiftInvariantMixture
      (fun v : Vertex e.val => ENNReal.ofReal (StatementIngredients.cellArea (decode e) v))
      (labelLaw z G hG hwalk hext e) fun v => vertexCode e (some v) :=
  isShiftInvariantMixture_cellArea (decode e) (decode_geometry e)
    (isReflectedWalk_areaFamily e (hwalk e he)) (decode_connected e) (vertexCode e)
    (vertexCode_injective e) _ (codedTwoSidedLaw_labelLaw he)

/-! ### 2. The position is read off the labels at fixed times -/

/-- The rational-time reading determined by the labels alone. -/
noncomputable def graphCode (z : CellField) (e : Env) (ξ : ℚ → ℕ∞) : RatCode :=
  (ξ, fun q => repAt z e (ξ q))

theorem measurable_graphCode (z : CellField) (e : Env) : Measurable (graphCode z e) := by
  have h : ∀ q : ℚ, Measurable fun ξ : ℚ → ℕ∞ => repAt z e (ξ q) := fun q =>
    (measurable_repAt z).comp (measurable_const.prodMk (measurable_pi_apply q))
  exact measurable_id.prodMk (measurable_pi_iff.2 h)

/-- **At every fixed real time the position is the field at the label**, `ℚ_H`-almost
everywhere. -/
theorem ae_startMixture_coupled {e : Env} (he : e ∈ G) (t : ℝ) :
    ∀ᵐ x ∂(startMixture (flowSlotKernel z G hG hwalk hext) e),
      x.2.toFun t = repAt z e (x.1.toFun t) := by
  rw [startMixture, Measure.ae_sum_iff]
  intro v
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [ae_flowSlotKernel_fixed (hG := hG) (hext := hext) ⟨he, v.property⟩ t]
    with x hx
  obtain ⟨w, hl, hp⟩ := hx
  rw [hl, hp, repAt_natCast]

/-! ### 3. The lift to the carrier -/

/-- The label marginal of `ℚ_H` is the weighted mixture of the label laws. -/
theorem map_fst_startMixture {e : Env} :
    (startMixture (flowSlotKernel z G hG hwalk hext) e).map Prod.fst =
      weightedPathMixture
        (fun v : Vertex e.val => ENNReal.ofReal (StatementIngredients.cellArea (decode e) v))
        (labelLaw z G hG hwalk hext e) := by
  rw [startMixture, Measure.map_sum measurable_fst.aemeasurable, weightedPathMixture]
  congr 1
  funext v
  rw [Measure.map_smul _ measurable_fst.aemeasurable, labelLaw, StatementIngredients.cellArea,
    ENNReal.ofReal_toReal (cellVolume_pos_lt_top (decode e) (decode_geometry e) v).2.ne]

/-- **Two-sided real-time shift invariance of `ℚ_H = ∑_v a_v ℙ_H^v` on the flow carrier**, at every
gate environment and every deterministic real shift. -/
theorem measurePreserving_codingShift_startMixture {e : Env} (he : e ∈ G) (r : ℝ) :
    MeasurePreserving (codingShift r) (startMixture (flowSlotKernel z G hG hwalk hext) e)
      (startMixture (flowSlotKernel z G hG hwalk hext) e) := by
  set Q := startMixture (flowSlotKernel z G hG hwalk hext) e with hQ
  refine ⟨measurable_codingShift r, ext_of_map_ratRead ?_⟩
  have hsl : Measurable fun ω : CadlagPath ℕ∞ => fun q : ℚ => ω.toFun ((q : ℝ) + r) :=
    measurable_pi_iff.2 fun q => CadlagPath.measurable_eval _
  have hsm : Measurable fun x : FlowCoding => fun q : ℚ => x.1.toFun ((q : ℝ) + r) :=
    hsl.comp measurable_fst
  have hfm : Measurable fun x : FlowCoding => CadlagPath.ratEval x.1 :=
    CadlagPath.measurable_ratEval.comp measurable_fst
  have hM : (Q.map Prod.fst).map (fun ω : CadlagPath ℕ∞ => fun q : ℚ => ω.toFun ((q : ℝ) + r)) =
      (Q.map Prod.fst).map CadlagPath.ratEval := by
    rw [hQ, map_fst_startMixture]
    have hmix := (isShiftInvariantMixture_labelLaw (hG := hG) (hwalk := hwalk) (hext := hext) he).1 r
    have h1 : (fun ω : CadlagPath ℕ∞ => fun q : ℚ => ω.toFun ((q : ℝ) + r)) =
        CadlagPath.ratEval ∘ CadlagPath.timeShift r := rfl
    rw [h1, ← Measure.map_map CadlagPath.measurable_ratEval (CadlagPath.measurable_timeShift r),
      hmix.map_eq]
  have hshifted : ∀ᵐ x ∂Q,
      ratRead (codingShift r x) = graphCode z e (fun q : ℚ => x.1.toFun ((q : ℝ) + r)) := by
    have hall := ae_all_iff.2 fun q : ℚ =>
      ae_startMixture_coupled (hG := hG) (hwalk := hwalk) (hext := hext) he ((q : ℝ) + r)
    filter_upwards [hall] with x hx
    exact Prod.ext (funext fun q => rfl) (funext fun q => hx q)
  have hplain : ∀ᵐ x ∂Q, ratRead x = graphCode z e (CadlagPath.ratEval x.1) := by
    have hall := ae_all_iff.2 fun q : ℚ =>
      ae_startMixture_coupled (hG := hG) (hwalk := hwalk) (hext := hext) he (q : ℝ)
    filter_upwards [hall] with x hx
    exact Prod.ext (funext fun q => rfl) (funext fun q => hx q)
  have e1 : (Q.map (codingShift r)).map ratRead =
      (Q.map fun x : FlowCoding => fun q : ℚ => x.1.toFun ((q : ℝ) + r)).map (graphCode z e) := by
    rw [Measure.map_map measurable_ratRead (measurable_codingShift r),
      Measure.map_map (measurable_graphCode z e) hsm]
    exact Measure.map_congr hshifted
  have e2 : Q.map ratRead =
      (Q.map fun x : FlowCoding => CadlagPath.ratEval x.1).map (graphCode z e) := by
    rw [Measure.map_map (measurable_graphCode z e) hfm]
    exact Measure.map_congr hplain
  have e3 : (Q.map fun x : FlowCoding => fun q : ℚ => x.1.toFun ((q : ℝ) + r)) =
      (Q.map Prod.fst).map (fun ω : CadlagPath ℕ∞ => fun q : ℚ => ω.toFun ((q : ℝ) + r)) :=
    (Measure.map_map hsl measurable_fst).symm
  have e4 : (Q.map fun x : FlowCoding => CadlagPath.ratEval x.1) =
      (Q.map Prod.fst).map CadlagPath.ratEval :=
    (Measure.map_map CadlagPath.measurable_ratEval measurable_fst).symm
  rw [e1, e2, e3, e4, hM]

end Gate

/-! ### 4. At the similarity-closed gate -/

open ReflectedGMS.SimilarityClosedGate in
/-- **Shift invariance of `ℚ_H` for the closed-gate all-starts kernel**, at every gate
environment and every real shift, with no remaining input. -/
theorem measurePreserving_codingShift_closedSlotKernel (z : CellField)
    (hz : IsCellRepresentative z) {e : Env} (he : e ∈ similarityClosedGate) (r : ℝ) :
    MeasurePreserving (codingShift r) (startMixture (closedSlotKernel z hz) e)
      (startMixture (closedSlotKernel z hz) e) :=
  measurePreserving_codingShift_startMixture (hext := extensionGateAll_similarityClosedGate z hz) he r

end ReflectedGMS.FlowSlotShift
