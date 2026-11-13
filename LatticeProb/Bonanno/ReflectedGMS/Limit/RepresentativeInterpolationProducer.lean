/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.RepresentativeInterpolationProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.ContinuousInterpolationMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Forms.NonvertexContinuityEnvironment
import LatticeProb.Bonanno.ReflectedGMS.Limit.RepresentativeInterpolationReduction
import LatticeProb.Bonanno.ReflectedGMS.Spatial.LargeCellDiameterDecay
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.AreaClockRecurrence

/-!
# The construction half of `hlimit`, produced at the actual walk

`InterpolatedTwoClockReduction.RepresentativeInterpolationData` — the regular spatial extensions
of an arbitrary measurable cell-representative rule `z` along both area clocks, and the two
measurable continuous interpolations — is proved here for almost every environment, every walk
datum, every start, every lift pair satisfying the pathwise clock clauses and every
representative rule, from the main theorem's own hypotheses `MassTransport ν` and
`FiniteEnergyMoment ν` alone (`ae_representativeInterpolationData`).  The statement is verbatim
the `hdata` binder of
`InterpolatedTwoClockReduction.hlimit_of_ae_interpolation_data_of_scaling_limit`, so `hlimit`
now follows from the analytic half `TwoClockScalingLimit` alone (`hlimit_of_scaling_limit`).

## Route

* **The extension of `z` (manuscript `p:prop:pathsextend` for `z_{Y_s}`).**  The cutoff
  machinery that produced the harmonic extension applies verbatim to the coordinates of `z`:
  `hasSpatialCutoffs_representative` is `p:lem:spatialcutoffs` for `z`, whose three analytic
  inputs are its local bound (cells meeting a ball have bounded diameter), and its local energy
  `|z_H - z_{H'}| ≤ d_H + d_{H'}` against the diameter-weighted local mass
  (`restrictGraph_hasFiniteEnergy_coord_of_localPiMass`).  With it, the càdlàg extension on the
  summable fast clock and the no-jump property at nonvertex times
  (`NonvertexJumpsFromEnergyBudget`) transfer to the area clock exactly as for `Φ`
  (`ae_pathInputs_exponentialAreaPath`).
* **The walk properties** are the checked ones: right regularity (`IsReflectedWalk`), edge jumps
  and no boundary entrance (`SpatialExtensionChainJumps`), finite-cut avoidance
  (`FiniteCutPathEndExtension`), density of vertex times (`SpatialInfinityAvoidance`), and
  recurrence (`AreaClockRecurrence`, which gives that no sojourn is infinite).
* **`s:lem:largecells`** in the form `LargeCellsFinite` from the checked
  `Spatial.ae_finite_scaledNear_of_finiteEnergyMoment` (`largeCellsFinite_of_finite_scaledNear`).
* **The exact clock** inherits all path inputs through the eighth pathwise clock clause (the
  homeomorphic time change onto the exponential clock), by `PathInputs.of_timeChange`.
* **Construction and measurability**: `Process/ContinuousInterpolation` and
  `Process/ContinuousInterpolationMeasurable`, assembled through
  `RepresentativeInterpolationReduction.representativeInterpolationData_of_eval_measurable`.

No named input remains.  The measurable interpolation is built on the raw sample space: its
evaluations are pointwise limits of explicit measurable dyadic approximations, redefined to `0`
off a measurable null set, so no completion is involved.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.RepresentativeInterpolationProducer

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.PathwiseClockClauseLift ReflectedGMS.InvarianceAssemblyNoReturn
open ReflectedGMS.SpatialExtensionConstruction ReflectedGMS.ContinuousInterpolation
open ReflectedGMS.InterpolatedTwoClockReduction ReflectedGMS.RepresentativeInterpolationReduction

/-! ## `s:lem:largecells` in the form used by the interpolation -/

/-- Only finitely many cells meeting a bounded region are large, from the finiteness of the
scaled near-cell counts at the origin. -/
theorem largeCellsFinite_of_finite_scaledNear {V : Type*} (F : IndexedCells V)
    (hfin : ∀ n : ℕ,
      {v : V | (0 : Plane) ∈ Spatial.cellScaledNeighborhood (n : ℝ) (F.cell v)}.Finite) :
    LargeCellsFinite F := by
  intro R δ hδ
  set R' : ℝ := max R 1 with hR'def
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨n, hn⟩ := exists_nat_ge (R' / δ)
  refine (hfin n).subset ?_
  rintro v ⟨⟨x, hxc, hxb⟩, hd⟩
  have hv' : Hits F (Metric.closedBall (0 : Plane) R') v :=
    ⟨x, hxc, Metric.closedBall_subset_closedBall (le_max_left _ _) hxb⟩
  have hnδ : R' ≤ n * δ := (div_le_iff₀ hδ).1 hn
  refine Spatial.mem_cellScaledNeighborhood_zero_of_hits F (k := (n : ℝ)) (ε := δ / R')
    (R := R') (Nat.cast_nonneg n) ?_ hR'.le hv' ?_
  · rw [show (n : ℝ) * (δ / R') = (n * δ) / R' by ring, le_div_iff₀ hR', one_mul]
    exact hnδ
  · rw [div_mul_cancel₀ δ hR'.ne']
    exact hd.le

/-! ## `p:lem:spatialcutoffs` for the representatives -/

/-- **Local energy of a coordinate of the representatives**, from the `π`-part of the local
diameter-weighted mass: across an ordinary edge `|z_H - z_{H'}| ≤ d_H + d_{H'}`. -/
theorem restrictGraph_hasFiniteEnergy_coord_of_localPiMass {V : Type*} [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane) (hz : CellRepresentatives F z)
    (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.pi v.1)) (i : Fin 2) :
    (restrictGraph F.graph A).HasFiniteEnergy (fun v => z v.1 i) := by
  have hfirst := SpatialCutoff.summable_diamSq_mul_conductance_of_localPiMass F A hmass
  have hsecond : Summable (fun p : A × A =>
      F.graph.c p.1.1 p.2.1 * Metric.diam (F.cell p.2.1 : Set Plane) ^ 2) := by
    refine hfirst.prod_symm.congr fun p => ?_
    rcases p with ⟨v, w⟩
    simp only [Prod.swap_prod_mk]
    rw [F.graph.c_symm]
    ring
  apply Summable.of_nonneg_of_le
    (fun p => (restrictGraph F.graph A).gradSq_nonneg _ p) _
    ((hfirst.add hsecond).mul_left 2)
  intro p
  by_cases hc : F.graph.c p.1.1 p.2.1 = 0
  · simp [ReflectedWalk.ConductanceGraph.gradSq, restrictGraph, hc, Metric.diam_nonneg]
  · have hadj : F.graph.toSimpleGraph.Adj p.1.1 p.2.1 :=
      lt_of_le_of_ne (F.graph.c_nonneg _ _) (Ne.symm hc)
    obtain ⟨q, hqv, hqw⟩ := hF.2.2.2.2.2.2.2 hadj
    have hnorm : ‖z p.2.1 - z p.1.1‖ ≤
        Metric.diam (F.cell p.1.1 : Set Plane) + Metric.diam (F.cell p.2.1 : Set Plane) := by
      rw [← dist_eq_norm]
      calc dist (z p.2.1) (z p.1.1) ≤ dist (z p.2.1) q + dist q (z p.1.1) :=
            dist_triangle _ _ _
        _ ≤ Metric.diam (F.cell p.2.1 : Set Plane) + Metric.diam (F.cell p.1.1 : Set Plane) :=
            add_le_add (Metric.dist_le_diam_of_mem (F.cell p.2.1).isCompact.isBounded (hz _) hqw)
              (Metric.dist_le_diam_of_mem (F.cell p.1.1).isCompact.isBounded hqv (hz _))
        _ = _ := add_comm _ _
    have hinc : |z p.2.1 i - z p.1.1 i| ≤
        Metric.diam (F.cell p.1.1 : Set Plane) + Metric.diam (F.cell p.2.1 : Set Plane) := by
      have h1 := SpatialCutoff.abs_coord_le_norm (z p.2.1 - z p.1.1) i
      simp only [PiLp.sub_apply] at h1
      exact h1.trans hnorm
    have hsq : (z p.2.1 i - z p.1.1 i) ^ 2 ≤
        2 * (Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 +
          Metric.diam (F.cell p.2.1 : Set Plane) ^ 2) := by
      have hsquare := (sq_le_sq₀ (abs_nonneg _)
        (add_nonneg Metric.diam_nonneg Metric.diam_nonneg)).2 hinc
      rw [sq_abs] at hsquare
      nlinarith [hsquare, Metric.diam_nonneg (s := (F.cell p.1.1 : Set Plane)),
        Metric.diam_nonneg (s := (F.cell p.2.1 : Set Plane)),
        sq_nonneg (Metric.diam (F.cell p.1.1 : Set Plane) -
          Metric.diam (F.cell p.2.1 : Set Plane))]
    simp only [ReflectedWalk.ConductanceGraph.gradSq, restrictGraph]
    have hmul := mul_le_mul_of_nonneg_left hsq (F.graph.c_nonneg p.1.1 p.2.1)
    nlinarith

/-- **`p:lem:spatialcutoffs` for the coordinates of a representative rule `z`**, with the
cutoff radius measured by any other representative rule `y`: the manuscript's local diameter
bound and local mass bound suffice (no corrector is involved). -/
theorem hasSpatialCutoffs_representative {V : Type*} [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (y : V → Plane) (hy : CellRepresentatives F y) (z : V → Plane)
    (hz : CellRepresentatives F z) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hmass : ∀ R : ℝ, r₀ ≤ R →
      Summable (fun v : {v : V | Hits F (Metric.closedBall (0 : Plane) R) v} =>
        Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.pi v.1))
    (m : V → ℝ) (hm : ∀ v, 0 < m v) (hmsum : Summable m) :
    HasSpatialCutoffs F.graph m y z := by
  intro i R
  set ρ : ℝ := max (R : ℝ) r₀ with hρ
  have hρR : (R : ℝ) ≤ ρ := le_max_left _ _
  have hρr₀ : r₀ ≤ ρ := le_max_right _ _
  set D₀ : ℝ := (ρ + 1) / 100 with hD₀
  set P : ℝ := ρ + 1 + D₀ with hP
  have hr₀1 : r₀ ≤ ρ + 1 := by linarith
  have hD0 : 0 ≤ D₀ := by linarith
  have hr₀P : r₀ ≤ P := by linarith
  have hB : 0 ≤ P + P / 100 := by linarith
  have hDcol : ∀ v : V, ‖y v‖ < ρ + 1 → Metric.diam (F.cell v : Set Plane) ≤ D₀ := by
    intro v hv
    refine hD (ρ + 1) hr₀1 v ⟨y v, hy v, ?_⟩
    simpa using hv.le
  have hf : ∀ v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) P) v},
      |z v i| ≤ P + P / 100 := by
    rintro v ⟨x, hxc, hxb⟩
    have hxn : ‖x‖ ≤ P := by simpa using hxb
    have hdiam : Metric.diam (F.cell v : Set Plane) ≤ P / 100 := hD P hr₀P v ⟨x, hxc, hxb⟩
    have hdist : dist (z v) x ≤ Metric.diam (F.cell v : Set Plane) :=
      Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded (hz v) hxc
    have htri : ‖z v‖ ≤ dist (z v) x + ‖x‖ := by
      simpa only [dist_zero_right] using dist_triangle (z v) x 0
    exact (SpatialCutoff.abs_coord_le_norm (z v) i).trans (by linarith)
  obtain ⟨U, hU⟩ := SpatialCutoff.exists_hilbertDomain_eqOn_of_patch F hF y hy
    (fun v => z v i) (ρ := ρ) (D := D₀) (P := P) hB hD0 hDcol hP.ge hf (hmass P hr₀P)
    (restrictGraph_hasFiniteEnergy_coord_of_localPiMass F hF z hz _ (hmass P hr₀P) i)
    m hm hmsum
  exact ⟨U, hU.mono fun v hv => le_trans hv hρR⟩

/-! ## The path inputs along the exponential area clock -/

/-- **Almost surely, the exponential area path satisfies `PathInputs` for `z`.**  The inputs are
the environment-level local diameter and local mass bounds of `r:prop:log` for the canonical
representatives `lexMinField` from this start (`AlmostSureCutoffBounds`), the walk datum, and a
lift with the right collapse. -/
theorem ae_pathInputs_exponentialAreaPath (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (start : Vertex e.val) (z : CellField)
    (hz : IsCellRepresentative z) {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C)
    (ho : ‖lexMinField.at e start‖ ≤ r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : Vertex e.val,
      Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
      Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN (decode e)
          {v : Vertex e.val | Hits (decode e) (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2))
    (Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (hXexp : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      ∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) :
    ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      PathInputs (decode e) (z.at e) (fun t => exponentialAreaPath (decode e) D t ω) := by
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
  have hcontw : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      SpatialExtensionChainJumps.NoJumpsAtNonvertexTimes
        (fun t => Existence.process D (summableFastRate e D hG) t ω) (z.at e) :=
    NonvertexJumpsFromEnergyBudget.ae_noJumpsAtNonvertexTimes_of_cutoffs hwalkm hG hm' hmsum'
      (lexMinField.at e) (z.at e) hcut start hbdd
  have hdense : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Dense {t | ∃ v, Xexp t ω = Sum.inl v} :=
    SpatialInfinityAvoidance.dense_vertices_ae_of_isReflectedWalk (decode e)
      (Existence.processFamily D hG (areaRate (decode e))) hwalk start Xexp hXexp
  have hret : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ v : Vertex e.val, ∀ T : ℝ≥0,
      ∃ t, T ≤ t ∧ exponentialAreaPath (decode e) D t ω = some v :=
    AreaClockRecurrence.returnsToEveryVertex_exponentialAreaPath e D hG
      (AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
        e D hG hdat) start
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
  filter_upwards [hextw, hcontw, ae_isHomeomorphicTimeChange_summableFastRate e D hG hdat start,
    ae_noBoundaryEntrance_areaPath e D hG hdat start, ae_edgeJumps_areaPath e D hG hdat start,
    hcutav, hrc, hrci, hdense, hXexp, hret]
    with ω hext hcontω htcω hentω hedgeω hcutω hrcω hrciω hdω hXω hretω
  refine
    { rightRegular := ⟨hrcω, hrciω⟩
      edgeJumps := hedgeω
      avoidsCuts := hcutω
      leaves := ?_
      dense := ?_
      noBoundaryJumps := SpatialExtensionChainJumps.noBoundaryJumps_of_noBoundaryEntrance hentω
        (SpatialExtensionChainJumps.noJumpsAtNonvertexTimes_of_timeChange htcω hcontω)
      existsCadlag := exists_cadlag_extension_of_timeChange htcω hext }
  · intro r v _
    obtain ⟨u, hu⟩ := exists_ne v
    obtain ⟨t, ht, htu⟩ := hretω u (r + 1)
    exact ⟨t, lt_of_lt_of_le (lt_add_one r) ht,
      fun hv => hu (Option.some_injective _ (htu.symm.trans hv))⟩
  · refine Dense.mono ?_ hdω
    rintro t ⟨v, hv⟩
    exact ⟨v, (hXω t).symm.trans (congrArg collapse hv)⟩

/-! ## The construction half of `hlimit` -/

/-- **`RepresentativeInterpolationData` at the actual walk.**  The statement is verbatim the
`hdata` binder of `InterpolatedTwoClockReduction.hlimit_of_ae_interpolation_data_of_scaling_limit`;
its only hypotheses are the main theorem's own `MassTransport ν` and `FiniteEnergyMoment ν`. -/
theorem ae_representativeInterpolationData (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField) :
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          ∀ z : CellField, IsCellRepresentative z →
            RepresentativeInterpolationData e D hG z start Xexp Xexact := by
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hmt hFE.ne hMax,
    Spatial.ae_finite_scaledNear_of_finiteEnergyMoment ν hmt hFE.ne] with e hlog hscaled
  intro hnt D hG hdat start Xexp Xexact M hpcc z hz
  letI := hnt
  unfold PathwiseClockClauses at hpcc
  have hF := decode_geometry e
  have hL : LargeCellsFinite (decode e) := largeCellsFinite_of_finite_scaledNear (decode e) hscaled
  obtain ⟨r₀, C, hr₀, hC, ho, hD, hW⟩ := hlog (lexMinField.at e) start
  have hXexp : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      ∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω :=
    hpcc.mono fun ω hω => hω.1
  have hinexp := ae_pathInputs_exponentialAreaPath e D hG hdat start z hz hr₀ hC ho hD hW
    Xexp hXexp
  have hinexact : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      PathInputs (decode e) (z.at e) (fun t => exactAreaPath (decode e) D t ω) := by
    filter_upwards [hinexp, hpcc] with ω hin hω
    exact hin.of_timeChange hω.2.2.2.2.2.2.2.1
  obtain ⟨Iexp, hIexpm, hIexp⟩ := exists_measurable_interpolation
    (areaSampleLaw (decode e) D hG start) hF hL (hz e) (exponentialAreaPath (decode e) D)
    (measurable_exponentialAreaPath (decode e) D) hinexp
  obtain ⟨Iexact, hIexactm, hIexact⟩ := exists_measurable_interpolation
    (areaSampleLaw (decode e) D hG start) hF hL (hz e) (exactAreaPath (decode e) D)
    (measurable_exactAreaPath (decode e) D) hinexact
  refine representativeInterpolationData_of_eval_measurable e D hG z start Xexp Xexact
    (fun t ω => pathExtension (z.at e) (fun s => exponentialAreaPath (decode e) D s ω) t)
    (fun t ω => pathExtension (z.at e) (fun s => exactAreaPath (decode e) D s ω) t)
    Iexp Iexact hIexpm hIexactm ?_ ?_
  · filter_upwards [hinexp, hIexp, hpcc] with ω hin hI hω
    refine ⟨hin.regularSpatialExtension hω.1, ?_⟩
    rw [hI]
    exact hin.isContinuousInterpolation hF hL (hz e) hω.1
  · filter_upwards [hinexact, hIexact, hpcc] with ω hin hI hω
    refine ⟨hin.regularSpatialExtension hω.2.1, ?_⟩
    rw [hI]
    exact hin.isContinuousInterpolation hF hL (hz e) hω.2.1

end ReflectedGMS.RepresentativeInterpolationProducer
