/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.SpatialExtensionEnvironment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionCore
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionCadlag
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionChainJumps
import LatticeProb.Bonanno.ReflectedGMS.Process.PathwiseClockClauseLift
import LatticeProb.Bonanno.ReflectedGMS.Forms.CanonicalFastFormProcess
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteCutPathEndExtension
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialInfinityAvoidance
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ExactAreaClockCollapse
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.AreaClockAdmissibleDischarge

/-!
# The environment-level `hreg` producer (`p:prop:pathsextend`)

This is the `section Environment` of the former monolith
`Process/SpatialExtensionConstruction.lean`, rebuilt on top of the three split modules
`SpatialExtensionCore` (pathwise + time change), `SpatialExtensionCadlag` (the càdlàg
extension on a summable-speed clock) and `SpatialExtensionChainJumps` (the chain-level jump
and time-change clauses).

The end product `ae_hreg_of_cutoffs_and_continuity` is verbatim the `hreg` binder of
`Recurrence/ExactAreaClockCollapse.ae_hlift_of_regularSpatialExtension`, from exactly two
open inputs: the spatial cutoff family `hcut` (manuscript `p:lem:spatialcutoffs`) and the
nonvertex-time continuity clause `hcont` (the nonvertex half of `p:prop:purejump`).
The clock comparison `htc`, the edge-jump clause `hedge` and the no-entrance half of
`hnbj` are all discharged here from `SpatialExtensionChainJumps`.

Nothing in this file certifies `hcut`, `hcont` or any main theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.SpatialExtensionConstruction

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.PathwiseClockClauseLift ReflectedGMS.InvarianceAssemblyNoReturn

/-! ## The canonical summable fast rate -/

section Environment

/-- The canonical summable-speed fast rate dominating the admissible rate `D.rateFunction hG`
(`SummableFastSpeed.exists_summable_fast_speed`). -/
noncomputable def summableFastRate (e : Env) (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) : Vertex e.val → ℝ :=
  haveI : Nontrivial (Vertex e.val) := nontrivial_vertex e
  Classical.choose (FullNetworkForm.exists_summable_fast_speed (decode e).graph hG
    (D.rateFunction hG) (D.rateFunction_pos hG))

theorem summableFastRate_spec (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) :
    (∀ v, 0 < summableFastRate e D hG v) ∧
    (∀ v, D.rateFunction hG v ≤ summableFastRate e D hG v) ∧
    (∀ v, 0 < (decode e).graph.pi v / summableFastRate e D hG v) ∧
    Summable (fun v => (decode e).graph.pi v / summableFastRate e D hG v) :=
  haveI : Nontrivial (Vertex e.val) := nontrivial_vertex e
  Classical.choose_spec (FullNetworkForm.exists_summable_fast_speed (decode e).graph hG
    (D.rateFunction hG) (D.rateFunction_pos hG))

/-- The summable speed measure `π / w` of the canonical fast rate. -/
noncomputable def fastSpeed (e : Env) (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (v : Vertex e.val) : ℝ :=
  (decode e).graph.pi v / summableFastRate e D hG v

/-- **`RegularSpatialExtension` for one environment and one start**, from a càdlàg
vertex-agreeing extension of the area path together with the two pathwise inputs.  The
right-regularity, finite-cut avoidance and vertex-time density are the checked properties of
the actual area-clock reflected walk.  The extension process `M` is chosen pathwise; no
measurability of `M` is claimed or needed here. -/
theorem exists_regularSpatialExtension_of_inputs (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (Φ : CellField) (start : Vertex e.val) {hmin : (decode e).graph.EnergyMinimizer}
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hrate : ∀ v, 0 < areaRate (decode e) v)
    (hext : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
      ∀ t x, exponentialAreaPath (decode e) D t ω = some x → Z t = Φ.at e x)
    (hnbj : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      NoBoundaryJumps (fun t => exponentialAreaPath (decode e) D t ω) (Φ.at e))
    (hedge : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      EdgeJumps (decode e) (fun t => exponentialAreaPath (decode e) D t ω))
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (hXexp : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
      IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
      AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)) :
    ∃ M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane,
      ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
        RegularSpatialExtension (decode e) (Φ.at e) (fun t => Xexp t ω) (fun t => M t ω) := by
  refine ⟨fun t ω => Classical.epsilon (fun Z : ℝ≥0 → Plane => IsCadlag Z ∧
    ∀ t x, exponentialAreaPath (decode e) D t ω = some x → Z t = Φ.at e x) t, ?_⟩
  have hdense : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Dense {t : ℝ≥0 | ∃ v, Xexp t ω = Sum.inl v} :=
    SpatialInfinityAvoidance.dense_vertices_ae_of_isReflectedWalk (decode e)
      (Existence.processFamily D hG (areaRate (decode e))) hwalk start Xexp
      (hXexp.mono fun ω hω => hω.1)
  have hcutav : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      AvoidsFiniteCutsAtNonvertexTimes (fun t => exponentialAreaPath (decode e) D t ω) :=
    FiniteCutPathEndExtension.reflected_ae_eventually_notMem_finiteCut hwalk hG hrate start
  have hrc : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
      (∃ x, exponentialAreaPath (decode e) D t ω = some x) →
        ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Ico t (t + ε),
          exponentialAreaPath (decode e) D s ω = exponentialAreaPath (decode e) D t ω :=
    (hwalk start).2.2.1
  have hrci : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
      exponentialAreaPath (decode e) D t ω = none → ∀ y : Vertex e.val,
        ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Ioo t (t + ε),
          exponentialAreaPath (decode e) D s ω ≠ some y :=
    (hwalk start).2.2.2.1
  filter_upwards [hext, hnbj, hedge, hXexp, hdense, hcutav, hrc, hrci]
    with ω hω hn he hX hd hc hrcω hrciω
  obtain ⟨hZ, hvert⟩ := Classical.epsilon_spec (p := fun Z : ℝ≥0 → Plane => IsCadlag Z ∧
    ∀ t x, exponentialAreaPath (decode e) D t ω = some x → Z t = Φ.at e x) hω
  exact regularSpatialExtension_of_inputs (decode e) (Xexp := fun t => Xexp t ω)
    (X := fun t => exponentialAreaPath (decode e) D t ω) hX.1 hZ hvert hn he ⟨hrcω, hrciω⟩
    hc hd

/-- **The `hreg` input of `ExactAreaClockCollapse.ae_hlift_of_regularSpatialExtension`, from
four named inputs.**  The statement is verbatim the `hreg` binder of that theorem.  The
càdlàg extension is built on the canonical summable fast clock and transported to the area
clock by `htc`.  Of the four binders, `htc`, `hedge` and the no-entrance half of `hnbj` are
discharged downstream in `ae_hreg_of_cutoffs_and_continuity`; `hcut` and the nonvertex half
of `hnbj` remain open, and nothing here certifies them. -/
theorem ae_hreg_of_inputs (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hcut : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        HasSpatialCutoffs (decode e).graph (fastSpeed e D hG) (lexMinField.at e) (Φ.at e))
    (htc : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            IsHomeomorphicTimeChange (fun t => exponentialAreaPath (decode e) D t ω)
              (fun t => Existence.process D (summableFastRate e D hG) t ω))
    (hnbj : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            NoBoundaryJumps (fun t => exponentialAreaPath (decode e) D t ω) (Φ.at e))
    (hedge : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            EdgeJumps (decode e) (fun t => exponentialAreaPath (decode e) D t ω)) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
            (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
              (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
              IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
              AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)) →
            ∃ M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane,
              ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
                RegularSpatialExtension (decode e) (Φ.at e)
                  (fun t => Xexp t ω) (fun t => M t ω) := by
  intro n
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [hcut, htc n, hnbj n, hedge n,
    AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hmt hFE.ne hMax]
    with e hcute htce hnbje hedgee hlog
  intro hn hnt D hG hdat Xexp hXexp
  letI := hnt
  have hcutΦ := hcute hnt D hG hdat
  have htcω := htce hn hnt D hG hdat
  have hnbjω := hnbje hn hnt D hG hdat
  have hedgeω := hedgee hn hnt D hG hdat
  obtain ⟨hmin, hrate, hwalk, -⟩ := hdat
  obtain ⟨hw, hdom, hm, hmsum⟩ := summableFastRate_spec e D hG
  have hwalkw : IsReflectedWalk (decode e).graph (summableFastRate e D hG) hmin
      (Existence.processFamily D hG (summableFastRate e D hG)) :=
    canonical_isReflectedWalk_of_rate_le D hG hmin (summableFastRate e D hG) hw hdom
  have hrateq : (fun v => (decode e).graph.pi v / fastSpeed e D hG v) =
      summableFastRate e D hG := by
    funext v
    show (decode e).graph.pi v / ((decode e).graph.pi v / summableFastRate e D hG v) = _
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ ((decode e).graph.pi_pos_of_connected hG v).ne']
  have hwalkm : IsReflectedWalk (decode e).graph
      (fun v => (decode e).graph.pi v / fastSpeed e D hG v) hmin
      (Existence.processFamily D hG (summableFastRate e D hG)) := by
    rw [hrateq]
    exact hwalkw
  have hm' : ∀ v, 0 < fastSpeed e D hG v := hm
  have hmsum' : Summable (fastSpeed e D hG) := hmsum
  obtain ⟨r₀, C, hr₀, hC, ho, hD, hW⟩ := hlog (lexMinField.at e) ⟨n, hn⟩
  have hbdd := LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime
    (decode e) (decode_geometry e) (lexMinField.at e) (isCellRepresentative_lexMinField e)
    (Existence.processFamily D hG (summableFastRate e D hG)) hwalkw hw ⟨n, hn⟩ hr₀ hC ho hD hW
  have hextw := ae_exists_cadlag_vertex_extension hwalkm hG hm' hmsum' (lexMinField.at e)
    (Φ.at e) hcutΦ ⟨n, hn⟩ hbdd
  have hext : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩), ∃ Z : ℝ≥0 → Plane,
      IsCadlag Z ∧ ∀ t x, exponentialAreaPath (decode e) D t ω = some x → Z t = Φ.at e x := by
    have hextw' : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩), ∃ W : ℝ≥0 → Plane,
        IsCadlag W ∧ ∀ t x, Existence.process D (summableFastRate e D hG) t ω = some x →
          W t = Φ.at e x := hextw
    filter_upwards [hextw', htcω] with ω hW htcω'
    exact exists_cadlag_extension_of_timeChange htcω' hW
  exact exists_regularSpatialExtension_of_inputs e D hG Φ ⟨n, hn⟩ hwalk hrate hext hnbjω
    hedgeω Xexp hXexp

/-! ## Three of the four inputs of `ae_hreg_of_inputs`, discharged at one environment

Each of the three is unconditional given `EnvironmentWalkData`: the area-clock (3.16)
summability it supplies is exactly the hypothesis that
`Process/SpatialExtensionChainJumps` needs. -/

/-- **`htc` at one environment and one start.**  The area clock is a homeomorphic time change
of the canonical summable fast clock, because the latter dominates the admissible rate
(`SpatialExtensionChainJumps.ae_isHomeomorphicTimeChange_of_rateFunction_le`). -/
theorem ae_isHomeomorphicTimeChange_summableFastRate (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (z : Vertex e.val) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG z),
      IsHomeomorphicTimeChange (fun t => exponentialAreaPath (decode e) D t ω)
        (fun t => Existence.process D (summableFastRate e D hG) t ω) :=
  SpatialExtensionChainJumps.ae_isHomeomorphicTimeChange_of_rateFunction_le
    (decode e) D hG (areaRate_pos e) (summableFastRate e D hG)
    (summableFastRate_spec e D hG).1 (summableFastRate_spec e D hG).2.1 z
    (areaClock_holdingTimesSummable e D hG
      (AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
        e D hG hdat) z)

/-- **`hedge` at one environment and one start**
(`SpatialExtensionChainJumps.ae_edgeJumps_process` at the area rate). -/
theorem ae_edgeJumps_areaPath (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (z : Vertex e.val) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG z),
      EdgeJumps (decode e) (fun t => exponentialAreaPath (decode e) D t ω) :=
  SpatialExtensionChainJumps.ae_edgeJumps_process (decode e) D hG (areaRate (decode e))
    (areaRate_pos e) z
    (areaClock_holdingTimesSummable e D hG
      (AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
        e D hG hdat) z)

/-- **The vertex half of `hnbj` at one environment and one start**: the area path never enters
a cell directly from the nonvertex state.  Local finiteness is `Geometry` clause 7. -/
theorem ae_noBoundaryEntrance_areaPath (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (z : Vertex e.val) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG z),
      SpatialExtensionChainJumps.NoBoundaryEntrance
        (fun t => exponentialAreaPath (decode e) D t ω) :=
  SpatialExtensionChainJumps.ae_noBoundaryEntrance_process (decode e)
    (decode_geometry e).neighborSet_finite D hG (areaRate (decode e)) (areaRate_pos e) z
    (areaClock_holdingTimesSummable e D hG
      (AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
        e D hG hdat) z)

/-! ## `hreg` from two open inputs -/

/-- **The `hreg` input of `ExactAreaClockCollapse.ae_hlift_of_regularSpatialExtension`, from
exactly two open inputs.**  The conclusion is verbatim the `hreg` binder of that theorem.

The two remaining inputs are:
* `hcut` — the spatial cutoff family of manuscript `p:lem:spatialcutoffs`, for the canonical
  summable speed `fastSpeed` and the canonical cell representatives `lexMinField`;
* `hcont` — the nonvertex-time half of manuscript `p:prop:purejump`, on the canonical
  summable fast clock.

The clock comparison `htc`, the edge-jump clause `hedge` and the no-entrance half of the
boundary-jump clause are discharged here from `Process/SpatialExtensionChainJumps`, using only
the area-clock (3.16) summability carried by `EnvironmentWalkData`.  Nothing here certifies
`hcut`, `hcont` or any main theorem. -/
theorem ae_hreg_of_cutoffs_and_continuity (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hcut : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        HasSpatialCutoffs (decode e).graph (fastSpeed e D hG) (lexMinField.at e) (Φ.at e))
    (hcont : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            SpatialExtensionChainJumps.NoJumpsAtNonvertexTimes
              (fun t => Existence.process D (summableFastRate e D hG) t ω) (Φ.at e)) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
            (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
              (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
              IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
              AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)) →
            ∃ M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane,
              ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
                RegularSpatialExtension (decode e) (Φ.at e)
                  (fun t => Xexp t ω) (fun t => M t ω) := by
  refine ae_hreg_of_inputs ν hmt hFE Φ hcut (fun n => ?_) (fun n => ?_) (fun n => ?_)
  · refine Filter.Eventually.of_forall fun e => ?_
    intro hn hnt D hG hdat
    letI := hnt
    exact ae_isHomeomorphicTimeChange_summableFastRate e D hG hdat ⟨n, hn⟩
  · filter_upwards [hcont n] with e hconte
    intro hn hnt D hG hdat
    letI := hnt
    filter_upwards [ae_isHomeomorphicTimeChange_summableFastRate e D hG hdat ⟨n, hn⟩,
      ae_noBoundaryEntrance_areaPath e D hG hdat ⟨n, hn⟩, hconte hn hnt D hG hdat]
      with ω htcω hentω hcontω
    exact SpatialExtensionChainJumps.noBoundaryJumps_of_noBoundaryEntrance hentω
      (SpatialExtensionChainJumps.noJumpsAtNonvertexTimes_of_timeChange htcω hcontω)
  · refine Filter.Eventually.of_forall fun e => ?_
    intro hn hnt D hG hdat
    letI := hnt
    exact ae_edgeJumps_areaPath e D hG hdat ⟨n, hn⟩

end Environment

end ReflectedGMS.SpatialExtensionConstruction
