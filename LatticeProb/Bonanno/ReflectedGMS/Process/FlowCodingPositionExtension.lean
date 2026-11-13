/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.FlowCodingPositionExtension at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.RepresentativeInterpolationProducer
import LatticeProb.Bonanno.ReflectedGMS.Temporal.TwoSidedRegenerationCoding

/-!
# (B3) The representative path of the actual area walk extends to a càdlàg planar path

Requirement (B3) of the carrier bridge (`outputs/regeneration-flow-handoff.2026-09-18.md` §4):
the position coordinate `P` of the flow carrier must be a càdlàg planar path that reads the
representative field at vertex times.  This is `p:prop:pathsextend` for the representative path
`z_{Y_s}`, and it is ALREADY a checked consequence of the main theorem's own hypotheses: the
construction half of `hlimit` (`Limit/RepresentativeInterpolationProducer`) proves it inside
`ae_pathInputs_exponentialAreaPath` (clause `existsCadlag`) for every measurable
cell-representative rule `z`, from the log-cutoff bounds of `r:prop:log` (MTP + FE) and the
càdlàg extension on the canonical summable fast clock transported along the homeomorphic time
change onto the area clock.

That lemma also asks for an end-labelled lift `Xexp`, used only for the density of vertex times.
`ae_exists_cadlag_extension_areaFamily` below re-runs exactly the `existsCadlag` part of its proof
(same producers, same order) without the lift, at the regeneration kernel's canonical exhaustion
and area-clock family `TwoSidedRegenerationCoding.areaFamily e`, from every start, at almost every
admissible environment.

No new mathematics; nothing here certifies `p:prop:pathsextend` beyond the cited producers or
either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.FlowCodingPositionExtension

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.SpatialExtensionConstruction ReflectedGMS.RepresentativeInterpolationProducer
open ReflectedGMS.TwoSidedRegenerationCoding

/-- **(B3) at the actual walk.**  For a measurable cell-representative rule `z`, at almost every
environment (MTP + FE), if the environment is admissible then from every start the area walk
`areaFamily e` has, almost surely, a càdlàg planar path agreeing with `z` at every vertex time. -/
theorem ae_exists_cadlag_extension_areaFamily (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (z : CellField)
    (hz : IsCellRepresentative z) :
    ∀ᵐ e ∂ν, EnvironmentAreaClockAdmissible e → ∀ start : Vertex e.val,
      ∀ᵐ ω ∂(areaFamily e).P start, ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
        ∀ t v, (areaFamily e).X t ω = some v → Z t = z.at e v := by
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hmt hFE.ne hMax]
    with e hlog
  intro hadm start
  letI : Nontrivial (Vertex e.val) := nontrivial_vertex e
  set D : (decode e).graph.Exhaustion := exhaustion e with hDdef
  set hG : (decode e).graph.toSimpleGraph.Connected := decode_connected e with hGdef
  have hdat : EnvironmentWalkData e D hG :=
    environmentWalkData_of_areaClockReachesLevelZeroIndices e D hG
      (areaClockReaches_exhaustion e hadm)
  obtain ⟨r₀, C, hr₀, hC, ho, hD, hW⟩ := hlog (lexMinField.at e) start
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

end ReflectedGMS.FlowCodingPositionExtension
