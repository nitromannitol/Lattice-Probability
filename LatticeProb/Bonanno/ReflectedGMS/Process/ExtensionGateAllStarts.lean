/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ExtensionGateAllStarts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.FlowCodingPositionExtension
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SimilarityClosedGate
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowCodingKernel
import LatticeProb.Bonanno.ReflectedGMS.Limit.InteriorRepresentative
import LatticeProb.Bonanno.ReflectedGMS.Limit.FlowCodingFrontier

/-!
# (B3) The position-extension gate, pointwise on the similarity-closed gate, at every start

Item F of `outputs/final-route-review.2026-09-18.md`.  The bridge kernel
`FlowCodingKernel.flowKernel z G hG hwalk hext` takes `hext : ExtensionGate z G`: at every live
environment the representative path of the area walk from the root cell extends càdlàg almost
surely (manuscript `p:prop:pathsextend`, tex ~1340).  The existing producer
`FlowCodingPositionExtension.ae_exists_cadlag_extension_areaFamily` gives it for `ν`-a.e.
environment only.

## What the a.e. producer actually uses

Reading its proof, EVERY ingredient is deterministic in the environment and almost sure in the
PATH, except one:

* `AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses` — the tuple `(r₀, C, hD, hW)` of
  `r:prop:log` (local diameter bound `hD` and local mass bound `hW` from radius `r₀` on).  This is
  the ONLY `ν`-a.e. step, and it is an ENVIRONMENT-ONLY statement (no path law).
* everything else — `EnvironmentWalkData` from admissibility, the summable fast clock,
  `hasSpatialCutoffs_representative` (deterministic from `hD` + finiteness of `hW`),
  `LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime` (path-a.s.
  from the tuple), `SpatialExtensionCadlag.ae_exists_cadlag_vertex_extension` (path-a.s. from
  the cutoffs), `ae_isHomeomorphicTimeChange_summableFastRate` (path-a.s. from walk data) and
  `SpatialExtensionConstruction.exists_cadlag_extension_of_timeChange` (pathwise) — holds at
  EVERY admissible environment, from EVERY start.

`RegularSpatialExtension`, `ae_hreg_of_cutoffs_and_continuity` and `NonvertexContinuity*`
(uniqueness, local boundedness, ordinary jumps, nonvertex-time continuity) are NOT used: B3 only
needs EXISTENCE of a càdlàg extension through `z` at vertex times.

The similarity-closed gate `G = {GoodEnvironment ∧ EventualBallBound}` already produces the tuple
POINTWISE (this is how `SimilarityClosedGate.environmentAreaClockGeometry_of_mem` is proved), so
no sub-gate is needed.

## Form of the statement

The extension is genuinely only almost sure in the PATH (the fast-clock path limits and the
bounded-range event are a.s. events of the walk), so the pointwise form is:

  for EVERY `e ∈ similarityClosedGate`, EVERY start vertex `v`, `ℙ_e^v`-a.s. the extension exists.

This is `extensionAllStarts_of_mem_similarityClosedGate` (any cell-representative rule `z`;
covariance of `z` is NOT needed), specialised to `z = interiorField` in
`extensionAllStarts_interiorField`.

## Results

* (a) `extensionAllStarts_of_mem_similarityClosedGate`, `extensionAllStarts_interiorField`;
* (b) `extensionGateSet z := similarityClosedGate ∩ {ExtensionAllStarts z}` EQUALS the gate
  (`extensionGateSet_eq`), hence is measurable, conull under MTP + FE, admissible, and closed
  under every physical similarity (`mem_extensionGateSet_iff_of_isSimilarity`), the translation
  and scaling environment maps included; `extensionAllStarts_of_isSimilarity` transports the
  statement along similarities from a gate member;
* (c) `extensionGate_similarityClosedGate` (any `z` with `IsCellRepresentative z`) and the drop-in
  `extensionGate_interiorField_similarityClosedGate : ExtensionGate interiorField
  similarityClosedGate` (the binder `hextC` of
  `CellRootedRegenerativeInvariance.regenerativeInvariance_cellRootedLaw_flowKernel_closedGate`);
  `closedGateFlowKernel`, the bridge kernel at the closed gate with NO remaining input, and
  `compProd_closedGateFlowKernel` (its annealed law equals that of any conull admissible
  extension gate).

Nothing here certifies `p:prop:pathsextend` beyond the cited producers, `hplain`, `hregen` or
either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.ExtensionGateAllStarts

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.SpatialExtensionConstruction ReflectedGMS.RepresentativeInterpolationProducer
open ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.AreaClockFastSpeedOccupation ReflectedGMS.GoodEnvironmentSet
open ReflectedGMS.NonmacroscopicSelectedBlocks ReflectedGMS.SimilarityClosedGate
open ReflectedGMS.FlowCodingKernel ReflectedGMS.InteriorRepresentative
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow

/-! ### 1. The `r:prop:log` tuple, pointwise on the gate -/

/-- **The log-cutoff tuple at every gate member**, for every representative rule and root.
This is the ONLY environment input of the a.e. producer, and the gate encodes it pointwise
(the eventual ball bound is read only at radii `≥ r₀`). -/
theorem logCutoff_of_mem_similarityClosedGate {e : Env} (he : e ∈ similarityClosedGate)
    (y : Vertex e.val → Plane) (o : Vertex e.val) :
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ‖y o‖ ≤ r₀ ∧
      (∀ R : ℝ, r₀ ≤ R → ∀ v : Vertex e.val,
        Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
        Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100) ∧
      (∀ R : ℝ, r₀ ≤ R →
        LogCutoff.localMassENN (decode e)
            {v : Vertex e.val | Hits (decode e) (Metric.closedBall (0 : Plane) R) v}
          ≤ ENNReal.ofReal (C * R ^ 2)) := by
  obtain ⟨⟨-, hsub⟩, M, hM, r₁, hr⟩ := he
  obtain ⟨R₀, hR₀pos, hR₀⟩ :=
    AlmostSureCutoffBounds.exists_diameter_bound_of_maxDiamHittingBall_sublinear (decode e) hsub
  have hr₀ : 0 < max (max R₀ ‖y o‖) r₁ :=
    lt_of_lt_of_le hR₀pos (le_trans (le_max_left _ _) (le_max_left _ _))
  have hD : ∀ R : ℝ, max (max R₀ ‖y o‖) r₁ ≤ R → ∀ v : Vertex e.val,
      Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
      Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100 :=
    fun R hR v hv => hR₀ R (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR) v hv
  exact ⟨max (max R₀ ‖y o‖) r₁, 2 * M.toReal, hr₀, by positivity,
    le_trans (le_max_right _ _) (le_max_left _ _), hD,
    localMassENN_hittingBall_le_of_eventualBallBound (decode e) (decode_geometry e) hr₀
      (le_max_right _ _) hD hM hr⟩

/-! ### 2. The deterministic-in-`e` core of the a.e. producer -/

/-- **(B3) at ONE environment, from EVERY start**, from admissibility and the `r:prop:log`
tuple at the canonical representatives and that start.  This is the body of
`FlowCodingPositionExtension.ae_exists_cadlag_extension_areaFamily` with its only `ν`-a.e. input
(`hlog`) made a hypothesis; every other step is path-a.s. at a fixed environment. -/
theorem ae_exists_cadlag_extension_areaFamily_of_logCutoff (e : Env)
    (hadm : EnvironmentAreaClockAdmissible e) (z : CellField) (hz : IsCellRepresentative z)
    (start : Vertex e.val)
    (hlog : ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ‖lexMinField.at e start‖ ≤ r₀ ∧
      (∀ R : ℝ, r₀ ≤ R → ∀ v : Vertex e.val,
        Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
        Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100) ∧
      (∀ R : ℝ, r₀ ≤ R →
        LogCutoff.localMassENN (decode e)
            {v : Vertex e.val | Hits (decode e) (Metric.closedBall (0 : Plane) R) v}
          ≤ ENNReal.ofReal (C * R ^ 2))) :
    ∀ᵐ ω ∂(areaFamily e).P start, ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
      ∀ t v, (areaFamily e).X t ω = some v → Z t = z.at e v := by
  letI : Nontrivial (Vertex e.val) := nontrivial_vertex e
  set D : (decode e).graph.Exhaustion := exhaustion e with hDdef
  set hG : (decode e).graph.toSimpleGraph.Connected := decode_connected e with hGdef
  have hdat : EnvironmentWalkData e D hG :=
    environmentWalkData_of_areaClockReachesLevelZeroIndices e D hG
      (areaClockReaches_exhaustion e hadm)
  obtain ⟨r₀, C, hr₀, hC, ho, hD, hW⟩ := hlog
  have hdat' := hdat
  obtain ⟨hmin, hrate, hwalk, -⟩ := hdat'
  obtain ⟨hw, hdom, hm, hmsum⟩ := summableFastRate_spec e D hG
  have hwalkw : IsReflectedWalk (decode e).graph (summableFastRate e D hG) hmin
      (Existence.processFamily D hG (summableFastRate e D hG)) :=
    canonical_isReflectedWalk_of_rate_le D hG hmin (summableFastRate e D hG) hw hdom
  have hrateq : (fun v => (decode e).graph.pi v / fastSpeed e D hG v) =
      summableFastRate e D hG := by
    funext v
    show (decode e).graph.pi v / ((decode e).graph.pi v / summableFastRate e D hG v) = _
    rw [div_div_eq_mul_div,
      mul_div_cancel_left₀ _ ((decode e).graph.pi_pos_of_connected hG v).ne']
  have hwalkm : IsReflectedWalk (decode e).graph
      (fun v => (decode e).graph.pi v / fastSpeed e D hG v) hmin
      (Existence.processFamily D hG (summableFastRate e D hG)) := by
    rw [hrateq]
    exact hwalkw
  have hm' : ∀ v, 0 < fastSpeed e D hG v := hm
  have hmsum' : Summable (fastSpeed e D hG) := hmsum
  have hcut : HasSpatialCutoffs (decode e).graph (fastSpeed e D hG) (lexMinField.at e)
      (z.at e) :=
    hasSpatialCutoffs_representative (decode e) (decode_geometry e) (lexMinField.at e)
      (isCellRepresentative_lexMinField e) (z.at e) (hz e) hr₀ hD
      (fun R hR => SpatialCutoffEnvironment.summable_diamSq_mul_pi_of_localMassENN_ne_top
        (decode e) _ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW R hR)))
      (fastSpeed e D hG) hm' hmsum'
  have hbdd := LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime
    (decode e) (decode_geometry e) (lexMinField.at e) (isCellRepresentative_lexMinField e)
    (Existence.processFamily D hG (summableFastRate e D hG)) hwalkw hw start hr₀ hC ho hD hW
  have hextw : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∃ W : ℝ≥0 → Plane,
      IsCadlag W ∧ ∀ t x, Existence.process D (summableFastRate e D hG) t ω = some x →
        W t = z.at e x :=
    ae_exists_cadlag_vertex_extension hwalkm hG hm' hmsum' (lexMinField.at e) (z.at e) hcut
      start hbdd
  have htc := ae_isHomeomorphicTimeChange_summableFastRate e D hG hdat start
  show ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
    ∀ t v, exponentialAreaPath (decode e) D t ω = some v → Z t = z.at e v
  filter_upwards [hextw, htc] with ω hext htcω
  exact SpatialExtensionConstruction.exists_cadlag_extension_of_timeChange htcω hext

/-! ### 3. (a) The all-starts statement, pointwise on the gate -/

/-- **The all-starts extension predicate at one environment**: from every start vertex, the
representative path of the area walk extends càdlàg almost surely. -/
def ExtensionAllStarts (z : CellField) (e : Env) : Prop :=
  ∀ start : Vertex e.val, ∀ᵐ ω ∂(areaFamily e).P start, ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
    ∀ t v, (areaFamily e).X t ω = some v → Z t = z.at e v

/-- **(a) B3 at EVERY gate environment and EVERY start**, for every cell-representative rule
(no covariance needed). -/
theorem extensionAllStarts_of_mem_similarityClosedGate (z : CellField)
    (hz : IsCellRepresentative z) {e : Env} (he : e ∈ similarityClosedGate) :
    ExtensionAllStarts z e := fun start =>
  ae_exists_cadlag_extension_areaFamily_of_logCutoff e
    (environmentAreaClockAdmissible_of_mem he) z hz start
    (logCutoff_of_mem_similarityClosedGate he (lexMinField.at e) start)

/-- **(a) at the interior representative.** -/
theorem extensionAllStarts_interiorField {e : Env} (he : e ∈ similarityClosedGate) :
    ExtensionAllStarts interiorField e :=
  extensionAllStarts_of_mem_similarityClosedGate interiorField
    isCellRepresentative_interiorField he

/-! ### 4. (b) The extension gate and its similarity invariance -/

/-! ### 5. (c) The drop-in `ExtensionGate` at the similarity-closed gate -/

/-- **`ExtensionGate z` at the similarity-closed gate**, for every cell-representative rule:
at a live environment the root vertex is one of the starts of (a). -/
theorem extensionGate_similarityClosedGate (z : CellField) (hz : IsCellRepresentative z) :
    ExtensionGate z similarityClosedGate := fun _ h =>
  extensionAllStarts_of_mem_similarityClosedGate z hz h.1 (rootVertex h)

/-- **(c) The drop-in**: `ExtensionGate interiorField similarityClosedGate` (the binder `hextC`
of `CellRootedRegenerativeInvariance.regenerativeInvariance_cellRootedLaw_flowKernel_closedGate`
and item F of the final-route review). -/
theorem extensionGate_interiorField_similarityClosedGate :
    ExtensionGate interiorField similarityClosedGate :=
  extensionGate_similarityClosedGate interiorField isCellRepresentative_interiorField

/-- **The bridge kernel at the similarity-closed gate and the interior representative**, with
NO remaining input (gate data and extension all discharged). -/
noncomputable def closedGateFlowKernel : Kernel Env FlowCoding :=
  flowKernel interiorField similarityClosedGate measurableSet_similarityClosedGate
    (fun _ he => environmentAreaClockAdmissible_of_mem he)
    extensionGate_interiorField_similarityClosedGate

/-- **Gate independence**: under MTP + (FE), the annealed law at the closed-gate kernel equals
the annealed law at ANY conull admissible extension gate (e.g. the a.e.-produced gate of
`CellRootedFrontierInterior.exists_gate_interiorField`). -/
theorem compProd_closedGateFlowKernel (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) {G : Set Env} (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGate interiorField G)
    (hGc : ν Gᶜ = 0) :
    ν ⊗ₘ flowKernel interiorField G hG hwalk hext = ν ⊗ₘ closedGateFlowKernel :=
  FlowCodingFrontier.compProd_flowKernel_congr ν hG measurableSet_similarityClosedGate hwalk
    (fun _ he => environmentAreaClockAdmissible_of_mem he) hext
    extensionGate_interiorField_similarityClosedGate hGc
    (measure_compl_similarityClosedGate ν hmt hFE)

end ReflectedGMS.ExtensionGateAllStarts
