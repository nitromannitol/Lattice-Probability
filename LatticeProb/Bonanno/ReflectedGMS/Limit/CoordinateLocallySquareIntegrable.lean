/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CoordinateLocallySquareIntegrable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoordinateLocallySquareIntegrableExit
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoordinateLocallySquareIntegrableLocalizer
import LatticeProb.Bonanno.ReflectedGMS.Forms.AreaFastClockIdentificationFiltration
import LatticeProb.Bonanno.ReflectedGMS.Forms.LocalHarmonicClockOrthogonality
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialCutoffEnvironment
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFormAssociationOptionalSampling
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyPotentialPathLimit
import LatticeProb.Bonanno.ReflectedGMS.Limit.BracketClausesScalarReduction
import LatticeProb.Bonanno.ReflectedGMS.Limit.CommonSquareLocalizer
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalMartingaleCombination
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.LogCutoffSpatialBoundedness
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureCutoffBounds
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy

/-!
# Bracket atom 1: `CoordinateLocallySquareIntegrable`

Each real coordinate `t ↦ M_t · i` of the pinned spatial extension `M` of the harmonic
coordinate along the exponential area path is a locally square-integrable martingale of the
completed area filtration.  This is manuscript `p:thm:martingale`: the local harmonicity of
`p:lem:localharm` on the **fast clock with summable speed** `m₀`, time changed to the area clock
("time change a local martingale by the inverses of the increasing adapted clock A").

## Assembly

For the radii `R_n` and the regions `A_n = {‖z‖ ≤ R_n/2}` of step (a):

* **fast side** — `N_n` = the full-energy path of the cutoff `U_n` stopped at the fast exit from
  `A_n` is a martingale of the completed fast filtration
  (`StoppedFormAssociation.martingale_stopped_fullEnergyPath_exit_completed`, with the variational
  test `hU` of step (a));
* **clock change** — `t ↦ N_n(h t)` is a martingale of the area filtration
  (`StoppedFormAssociation.martingale_stoppedValue_clock_of_bound_of_ae`), with the stopping times
  of `AreaFastClockStopping`, the filtration inclusion of step (c)
  (`AreaFastClockFiltration.areaFiltration_ae_le_measurableSpace_fastClock`), and the uniform bound
  of the pathwise identification;
* **identification** — on the good event of step (b), `M_{t ∧ σ_n} · i = U_n(start) + N_n(h t)`
  (`CoordinateLocallySquareIntegrableExit.stoppedProcess_coord_eq`), `σ_n` the area exit from `A_n`;
* **localization** — `σ_n` are stopping times of the area filtration, increasing, and tend to `⊤`
  because the area path is spatially bounded on bounded time windows.

The generic core is `martingale_memLp_of_clock`; the environment statement from explicit radii is
`coordinateLocallySquareIntegrable_of_radii`; the ν-level producer, in the exact shape of the
`hlocal` binder of `BracketClausesScalarReduction.hbracket_of_ae_scalar_inputs` restricted to
atom 1, is `ae_coordinateLocallySquareIntegrable`, from `MassTransport ν`, the (FE) moment and
`IsHarmonicCoordinate ν Φ` alone.  No hypothesis is `Summable (cellArea …)` or a global
`HasFiniteEnergy`; the only summable speed is the canonical `fastSpeed`.
-/

-- Merged from `ReflectedGMS/Forms/LocalHarmonicClockEnvironment.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_LocalHarmonicClockEnvironment

/-!
# `p:eq:parttest` at a random environment: the `hU` input from `hΦ` alone

This composes the deterministic step (a)
(`Forms/LocalHarmonicClockOrthogonality.hU_of_fullRectangleOrthogonality`) with the two
almost-sure environment producers it needs, so that the `hU` binder of
`Forms/StoppedFormAssociationFastStopped.martingale_stopped_fullEnergyPath_exit_completed`
becomes available from `IsHarmonicCoordinate ν Φ` — the `hΦ` binder of the four-input
invariance assembly — plus the assembly's own `MassTransport` and `FiniteEnergyMoment`.

The two producers are:

* `Process/SpatialCutoffEnvironment.ae_hasSpatialCutoffs_of_isHarmonicCoordinate`, the
  spatial cutoff family `p:lem:spatialcutoffs` for the **summable fast speed** `fastSpeed`
  and the canonical representatives `lexMinField` (the area speed never appears);
* `Spatial/AlmostSureCutoffBounds.ae_exists_diameter_bound`, the local diameter bound
  `diam (cell v) ≤ R/100` on cells meeting `B̄(0,R)`, which needs only mass transport and the
  (FE) moment — no maximal inequality.

The H5c clause itself is read off `hΦ` as `FullSpatialHarmonicity`'s first component.

The region produced is `A_R = {v | ‖z v‖ ≤ R/2}`, exactly the set whose spatial exit time is
the manuscript's localizer, and `U_R` is the cutoff at radius `R`; both are indexed by the
same natural number `R`, above one almost-surely finite threshold `R₀(e)`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.LocalHarmonicClockEnvironment

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients
open ReflectedWalk FullNetworkForm
open QuenchedFormulation
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.SpatialExtensionConstruction

/-- **Step (a) at a random environment.**  Almost surely there is a finite threshold `R₀`
such that, for every coordinate `i` and every integer radius `R ≥ R₀`, the spatial cutoff
`U` of `Φ · i` at radius `R` satisfies the *full spatial variational test* against every
element of the fast-speed Hilbert energy domain supported in `{‖z v‖ ≤ R/2}`.

This conclusion is verbatim the pair (cutoff identity, `hU` binder) consumed by
`StoppedFormAssociationFastStopped.martingale_stopped_fullEnergyPath_exit_completed` with
`A = {v | ‖z v‖ ≤ R/2}`. -/
theorem ae_exists_cutoff_and_hU_of_isHarmonicCoordinate (ν : Measure Env)
    [IsProbabilityMeasure ν] (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ) :
    ∀ᵐ e ∂ν, ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (i : Fin 2) (R : ℕ), R₀ ≤ (R : ℝ) →
            ∃ U : hilbertDomain (decode e).graph (fastSpeed e D hG),
              Set.EqOn (unweight (fastSpeed e D hG)
                  (valueInclusion (decode e).graph (fastSpeed e D hG) U))
                (fun v => (Φ.at e) v i)
                {v : Vertex e.val | ‖lexMinField.at e v‖ ≤ (R : ℝ)} ∧
              ∀ w : hilbertDomain (decode e).graph (fastSpeed e D hG),
                (∀ x ∉ {v : Vertex e.val | ‖lexMinField.at e v‖ ≤ (R : ℝ) / 2},
                  unweight (fastSpeed e D hG)
                    (valueInclusion (decode e).graph (fastSpeed e D hG) w) x = 0) →
                (decode e).graph.dirichletForm
                  (unweight (fastSpeed e D hG)
                    (valueInclusion (decode e).graph (fastSpeed e D hG) U))
                  (unweight (fastSpeed e D hG)
                    (valueInclusion (decode e).graph (fastSpeed e D hG) w)) = 0 := by
  filter_upwards
    [SpatialCutoffEnvironment.ae_hasSpatialCutoffs_of_isHarmonicCoordinate ν hmt hFE Φ hΦ,
      AlmostSureCutoffBounds.ae_exists_diameter_bound ν hmt hFE.ne,
      hΦ.2.2.2.2.1] with e hcut hdiam hΦe
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hdiam
  refine ⟨R₀, hR₀pos, ?_⟩
  intro hnt D hG hdata i R hR
  letI := hnt
  obtain ⟨U, hUeq⟩ := hcut hnt D hG hdata i R
  refine ⟨U, hUeq, ?_⟩
  have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le hR₀pos hR
  exact LocalHarmonicClock.hU_of_fullRectangleOrthogonality (decode_geometry e)
    (isCellRepresentative_lexMinField e) hΦe.2.2.1.1 hRpos (hR₀ (R : ℝ) hR)
    (fastSpeed e D hG) i U hUeq

end ReflectedGMS.LocalHarmonicClockEnvironment

end Merged_LocalHarmonicClockEnvironment

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.CoordinateLocallySquareIntegrableProof

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk FullNetworkForm
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.SpatialExtensionConstruction
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.BracketClausesScalarReduction
open ReflectedGMS.AreaFastClockStopping ReflectedGMS.AreaFastClockPath
open ReflectedGMS.AreaFastClockFiltration ReflectedGMS.AreaTimeChangeJumpLaw

/-! ## The generic core: clock change plus identification -/

section Core

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- **The clock-change core.**  If `N` is a bounded, right-continuous `F`-martingale, `h` a
monotone finite family of `F`-stopping times whose stopped σ-algebras contain `G` up to null
sets, and `Z` a `G`-adapted process with `Z_t = c + N_{h t}` almost surely at every time, then
`Z` is a square-integrable `G`-martingale. -/
theorem martingale_memLp_of_clock {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 m0} {N : ℝ≥0 → Ω → ℝ}
    (hN : Martingale N F P) (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => N t ω))
    {C : ℝ} (hC : ∀ᵐ ω ∂P, ∀ t, |N t ω| ≤ C)
    {h : ℝ≥0 → Ω → WithTop ℝ≥0} (hh : ∀ t, IsStoppingTime F (h t))
    (hmono : ∀ ω, Monotone (fun t => h t ω)) (hfin : ∀ t ω, h t ω ≠ ⊤)
    (hG : ∀ (t : ℝ≥0) (B : Set Ω), MeasurableSet[G t] B →
      ∃ B' : Set Ω, MeasurableSet[(hh t).measurableSpace] B' ∧ B =ᵐ[P] B')
    (hnullG : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[G t] A)
    {Z : ℝ≥0 → Ω → ℝ} (hZ : StronglyAdapted G Z) (c : ℝ)
    (hZN : ∀ t, ∀ᵐ ω ∂P, Z t ω = c + stoppedValue N (h t) ω) :
    Martingale Z G P ∧ ∀ t, MemLp (Z t) 2 P := by
  have hadapt : StronglyAdapted G (fun t ω => stoppedValue N (h t) ω) := by
    intro t
    have hsub : StronglyMeasurable[G t] (fun ω => Z t ω - c) :=
      (hZ t).sub stronglyMeasurable_const
    refine LocalMartingaleCombination.stronglyMeasurable_of_ae_eq_of_null_events (G.le t)
      (hnullG t) hsub ?_
    filter_upwards [hZN t] with ω hω
    rw [hω]
    ring
  have hNh : Martingale (fun t ω => stoppedValue N (h t) ω) G P :=
    StoppedFormAssociation.martingale_stoppedValue_clock_of_bound_of_ae hN hr hC hh hmono hfin
      hG hadapt
  have hsum : Martingale ((fun _ _ => c) + fun t ω => stoppedValue N (h t) ω) G P :=
    (martingale_const G P c).add hNh
  refine ⟨hsum.congr hZ fun t => ?_, fun t => ?_⟩
  · filter_upwards [hZN t] with ω hω
    rw [hω]
    rfl
  · refine MemLp.of_bound ((hZ t).mono (G.le t)).aestronglyMeasurable (|c| + C) ?_
    filter_upwards [hZN t, hC] with ω hω hCω
    rw [hω, Real.norm_eq_abs]
    calc |c + stoppedValue N (h t) ω| ≤ |c| + |stoppedValue N (h t) ω| := abs_add_le _ _
      _ ≤ |c| + C := by
          gcongr
          exact hCω _

end Core

/-! ## Small pathwise facts -/

section Pathwise

/-- The localized, stopped process of `Locally`, at a sample with positive stopping time. -/
theorem stoppedProcess_indicator_of_pos {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}
    {σ : Ω → WithTop ℝ≥0} {ω : Ω} (hω : ⊥ < σ ω) (t : ℝ≥0) :
    stoppedProcess (fun t => {ω | ⊥ < σ ω}.indicator (X t)) σ t ω =
      X (min (t : WithTop ℝ≥0) (σ ω)).untopA ω := by
  unfold stoppedProcess
  exact Set.indicator_of_mem (s := {ω | ⊥ < σ ω}) hω (X (min (t : WithTop ℝ≥0) (σ ω)).untopA)

/-- A stopped process read at a finite clock value. -/
theorem stoppedValue_stoppedProcess_coe {Ω : Type*} {N : ℝ≥0 → Ω → ℝ}
    {τ h : Ω → WithTop ℝ≥0} {ω : Ω} {a : ℝ≥0} (ha : h ω = (a : WithTop ℝ≥0)) :
    stoppedValue (stoppedProcess N τ) h ω = N (min (a : WithTop ℝ≥0) (τ ω)).untopA ω := by
  unfold stoppedValue stoppedProcess
  rw [ha]
  rfl

variable {V : Type*}

theorem inl_of_collapse_eq_some {F : IndexedCells V} {s : State F} {v : V}
    (h : collapse s = some v) : s = Sum.inl v := by
  cases s with
  | inl y =>
    simp only [collapse, Sum.elim_inl, Option.some.injEq] at h
    rw [h]
  | inr b => simp [collapse] at h

theorem exists_inr_of_collapse_eq_none {F : IndexedCells V} {s : State F}
    (h : collapse s = none) : ∃ b, s = Sum.inr b := by
  cases s with
  | inl y => simp [collapse] at h
  | inr b => exact ⟨b, rfl⟩

end Pathwise

/-! ## The environment level -/

section Environment

/-- The canonical summable fast walk. -/
noncomputable abbrev fastPF (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected) :
    ProcessFamily (Vertex e.val) :=
  Existence.processFamily D hG (summableFastRate e D hG)

/-- The actual area walk. -/
noncomputable abbrev areaPF (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected) :
    ProcessFamily (Vertex e.val) :=
  Existence.processFamily D hG (areaRate (decode e))

/-- The spatial region `{‖z‖ ≤ r}` of the lexicographic cell representatives. -/
abbrev region (e : Env) (r : ℝ) : Set (Vertex e.val) := {v | ‖lexMinField.at e v‖ ≤ r}

/-- **Bracket atom 1 at one environment, from explicit radii.**  The inputs are: radii `R_n`
increasing to `∞` with the local diameter bound, the two-sided comparison between `Φ` and the
cell representatives on the regions (a consequence of the sublinear corrector), the start inside
the first region, the step-(a) cutoffs with their variational test, and spatial boundedness of
the area path on bounded time windows. -/
theorem coordinateLocallySquareIntegrable_of_radii (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRmono : Monotone R)
    (hRtop : ∀ b : ℝ, ∃ n, b ≤ R n)
    (hD : ∀ (n : ℕ) (v : Vertex e.val),
      Hits (decode e) (Metric.closedBall (0 : Plane) (R n)) v →
        Metric.diam ((decode e).cell v : Set Plane) ≤ R n / 100)
    (K K' : ℕ → ℝ)
    (hzΦ : ∀ (n : ℕ) (v : Vertex e.val), ‖Φ.at e v‖ ≤ K n + 2 → ‖lexMinField.at e v‖ ≤ R n)
    (hΦA : ∀ (n : ℕ) (v : Vertex e.val), ‖lexMinField.at e v‖ ≤ R n / 2 → ‖Φ.at e v‖ ≤ K n)
    (hΦB : ∀ (n : ℕ) (v : Vertex e.val), ‖lexMinField.at e v‖ ≤ R n → ‖Φ.at e v‖ ≤ K' n)
    (hstart : ‖lexMinField.at e start‖ ≤ R 0 / 2)
    (hcut : ∀ (i : Fin 2) (n : ℕ), ∃ U : hilbertDomain (decode e).graph (fastSpeed e D hG),
      Set.EqOn (unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) U))
        (fun v => (Φ.at e) v i) (region e (R n)) ∧
      ∀ w : hilbertDomain (decode e).graph (fastSpeed e D hG),
        (∀ x ∉ region e (R n / 2),
          unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) w) x = 0) →
        (decode e).graph.dirichletForm
          (unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) U))
          (unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) w)) = 0)
    (hbdd : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      ∀ T : ℝ≥0, ∃ Mb : ℝ,
      ∀ t : ℝ≥0, t ≤ T → ∀ v, exponentialAreaPath (decode e) D t ω = some v →
        ‖lexMinField.at e v‖ ≤ Mb) :
    CoordinateLocallySquareIntegrable e D hG start M := by
  intro i
  obtain ⟨hmin, hrate, hwalkA, -⟩ := id hdat
  obtain ⟨hw, hdom, hm, hmsum⟩ := summableFastRate_spec e D hG
  haveI : IsFiniteMeasure (areaSampleLaw (decode e) D hG start).completion :=
    isFiniteMeasure_areaSampleLaw_completion e D hG start
  have hF : Geometry (decode e) := decode_geometry e
  have hz : CellRepresentatives (decode e) (lexMinField.at e) :=
    isCellRepresentative_lexMinField e
  have hwalkw : IsReflectedWalk (decode e).graph (summableFastRate e D hG) hmin
      (fastPF e D hG) :=
    canonical_isReflectedWalk_of_rate_le D hG hmin (summableFastRate e D hG) hw hdom
  have hrateq : (fun v => (decode e).graph.pi v / fastSpeed e D hG v) =
      summableFastRate e D hG := by
    funext v
    show (decode e).graph.pi v / ((decode e).graph.pi v / summableFastRate e D hG v) = _
    rw [div_div_eq_mul_div,
      mul_div_cancel_left₀ _ ((decode e).graph.pi_pos_of_connected hG v).ne']
  have hwalkm : IsReflectedWalk (decode e).graph
      (fun v => (decode e).graph.pi v / fastSpeed e D hG v) hmin (fastPF e D hG) := by
    rw [hrateq]
    exact hwalkw
  have hm' : ∀ v, 0 < fastSpeed e D hG v := hm
  have hmsum' : Summable (fastSpeed e D hG) := hmsum
  have hwalkA' : IsReflectedWalk (decode e).graph
      (fun v => (decode e).graph.pi v / cellArea (decode e) v) hmin (areaPF e D hG) := hwalkA
  have hHTSa := areaClock_holdingTimesSummable e D hG
    (AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
      e D hG hdat) start
  choose U hUeq hU using hcut i
  -- null events of the target filtration
  have hnullG : ∀ (t : ℝ≥0) (A : Set (NullMeasurableSpace (Existence.Sample (Vertex e.val))
      (areaSampleLaw (decode e) D hG start))),
      (areaSampleLaw (decode e) D hG start).completion A = 0 →
      MeasurableSet[areaFiltration e D (areaSampleLaw (decode e) D hG start) t] A :=
    fun t A hA => ProcessFiltration.measurableSet_completedNaturalFiltration_of_null _ _ _ t A hA
  -- (d1) the coordinate of `M` is adapted
  have hMadapt : StronglyAdapted (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun t ω => M t ω i) := by
    intro t
    let g : ℕ → ℝ := fun k =>
      match (Encodable.decode k : Option (Option (Vertex e.val))) with
      | some (some v) => (Φ.at e) v i
      | _ => 0
    have hg : ∀ v : Vertex e.val, g (Encodable.encode (some v)) = (Φ.at e) v i := by
      intro v
      simp only [g, Encodable.encodek]
    have hmeas : StronglyMeasurable[areaFiltration e D (areaSampleLaw (decode e) D hG start) t]
        (fun ω => g (observedState e (exponentialAreaPath (decode e) D t ω))) :=
      ((measurable_of_countable g).comp (measurable_completedNaturalFiltration
        (areaSampleLaw (decode e) D hG start)
        (fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
        (fun t => (measurable_of_countable (observedState e)).comp
          (measurable_exponentialAreaPath (decode e) D t)) t)).stronglyMeasurable
    refine LocalMartingaleCombination.stronglyMeasurable_of_ae_eq_of_null_events
      ((areaFiltration e D (areaSampleLaw (decode e) D hG start)).le t) (hnullG t) hmeas ?_
    refine StoppedFormAssociation.ae_completion_of_ae ?_
    have hvt : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
        ∃ x, exponentialAreaPath (decode e) D t ω = some x :=
      ((hwalkA start).2.1 t).mono fun _ hω => hω.1
    filter_upwards [hpcc, hvt] with ω hpω hvtω
    obtain ⟨hcol, -, -, -, -, -, -, -, -, hreg⟩ := hpω
    obtain ⟨x, hx⟩ := hvtω
    have hXexp : Xexp t ω = Sum.inl x := inl_of_collapse_eq_some ((hcol t).trans hx)
    have hMx : M t ω = (Φ.at e) x := hreg.1.2.1 t x hXexp
    show g (observedState e (exponentialAreaPath (decode e) D t ω)) = M t ω i
    rw [hx, hMx]
    exact hg x
  -- the localizing sequence: exits of the area path
  have hσstop : ∀ n : ℕ, IsStoppingTime (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2))) := fun n =>
    StoppedFormAssociation.isStoppingTime_completed_exitHitting (h := hwalkA') (z := start)
      (A := region e (R n / 2)) (henc := observedState_injective e)
      (X' := fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
      (hX'e := fun _ _ => rfl)
      (hX' := fun t => (measurable_of_countable (observedState e)).comp
        (measurable_exponentialAreaPath (decode e) D t))
  have hAmono : Monotone (fun n : ℕ => region e (R n / 2)) := by
    intro a b hab v hv
    have h1 := hRmono hab
    show ‖lexMinField.at e v‖ ≤ R b / 2
    have h2 : ‖lexMinField.at e v‖ ≤ R a / 2 := hv
    linarith
  have hposmeas : ∀ (n : ℕ) (t : ℝ≥0),
      MeasurableSet[areaFiltration e D (areaSampleLaw (decode e) D hG start) t]
        {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2)) ω} := by
    intro n t
    have h0 := hσstop n 0
    have hc := (areaFiltration e D (areaSampleLaw (decode e) D hG start)).mono
      (show (0 : ℝ≥0) ≤ t from zero_le) _ h0.compl
    convert hc using 1
    ext ω
    simp only [mem_setOf_eq, mem_compl_iff, not_le]
    exact Iff.rfl
  -- the localized stopped coordinate is adapted
  have hZadapt : ∀ n : ℕ, StronglyAdapted
      (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (R n / 2)) ω}.indicator (fun ω => M t ω i))
        (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2)))) := by
    intro n
    refine ProcessFiltration.stronglyAdapted_stoppedProcess_completedNaturalFiltration
      (areaSampleLaw (decode e) D hG start)
      (fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
      (fun t => (measurable_of_countable (observedState e)).comp
        (measurable_exponentialAreaPath (decode e) D t)) ?_ (hσstop n) ?_
    · intro t
      exact (hMadapt t).indicator (hposmeas n t)
    · refine StoppedFormAssociation.ae_completion_of_ae ?_
      filter_upwards [hpcc] with ω hpω
      obtain ⟨-, -, -, -, -, -, -, -, -, hreg⟩ := hpω
      intro t
      have hMr : ContinuousWithinAt (fun t => M t ω i) (Ioi t) t :=
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).continuousAt).comp_continuousWithinAt
          (hreg.1.1.isRightContinuous t)
      by_cases hω : ω ∈ {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (R n / 2)) ω}
      · exact hMr.congr (fun s _ => Set.indicator_of_mem hω (fun ω => M s ω i))
          (Set.indicator_of_mem hω (fun ω => M t ω i))
      · exact continuousWithinAt_const.congr
          (fun s _ => Set.indicator_of_notMem hω (fun ω => M s ω i))
          (Set.indicator_of_notMem hω (fun ω => M t ω i))
  -- almost-sure path facts of the area walk, independent of `n`
  have hrcA : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
      (∃ x, (areaPF e D hG).X t ω = some x) →
        ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Ico t (t + ε), (areaPF e D hG).X s ω = (areaPF e D hG).X t ω :=
    (hwalkA start).2.2.1
  have hentA : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      SpatialExtensionChainJumps.NoBoundaryEntrance (fun t => (areaPF e D hG).X t ω) :=
    SpatialExtensionChainJumps.ae_noBoundaryEntrance_process (decode e) hF.2.2.2.2.2.2.1 D hG
      (areaRate (decode e)) hrate start hHTSa
  have hedgeA : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      EdgeJumps (decode e) (fun t => (areaPF e D hG).X t ω) :=
    SpatialExtensionChainJumps.ae_edgeJumps_process (decode e) D hG (areaRate (decode e)) hrate
      start hHTSa
  have hdyA : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      ∀ s ∈ globalDyadicSupport, ∃ x, (areaPF e D hG).X s ω = some x :=
    (ae_ball_iff (μ := (areaPF e D hG).P start) globalDyadicSupport_countable).2
      fun s _ => ((hwalkA start).2.1 s).mono fun _ hω => hω.1
  have h0A : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      (areaPF e D hG).X 0 ω = some start :=
    Existence.ae_process_zero D hG (areaRate (decode e)) hrate start
  have hgp : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      ClockGood (decode e) (fastSpeed e D hG) (fastPF e D hG) ω ∧
        ∀ t : ℝ≥0, exponentialAreaPath (decode e) D t ω =
          areaTimeChangedPath (decode e) (fastSpeed e D hG) (fastPF e D hG) t ω :=
    ae_clockGood_and_exponentialAreaPath_eq e D hG hdat start
  -- the square-integrable martingale property of each localized coordinate
  have hcore : ∀ n : ℕ,
      Martingale (stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting
            (areaPF e D hG) (region e (R n / 2)) ω}.indicator (fun ω => M t ω i))
          (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2))))
        (areaFiltration e D (areaSampleLaw (decode e) D hG start))
        (areaSampleLaw (decode e) D hG start).completion ∧
      ∀ t, MemLp (stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting
            (areaPF e D hG) (region e (R n / 2)) ω}.indicator (fun ω => M t ω i))
          (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2))) t) 2
        (areaSampleLaw (decode e) D hG start).completion := by
    intro n
    have hN := StoppedFormAssociation.martingale_stopped_fullEnergyPath_exit_completed
      (h := hwalkm) (hG := hG) (hm := hm') (hmsum := hmsum') (default := start) (z := start)
      (U := U n) (A := region e (R n / 2)) (henc := observedState_injective e)
      (X' := fun t ω => observedState e (Existence.process D (summableFastRate e D hG) t ω))
      (hX'e := fun _ _ => rfl)
      (hX' := fun t => (measurable_of_countable (observedState e)).comp
        (Existence.measurable_process D (summableFastRate e D hG) t))
      (hU n)
    have hcadN : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
        IsCadlag (fun t => fullEnergyPotentialPathLimit (decode e).graph (fastSpeed e D hG) hm'
          (fastPF e D hG) start (U n) t ω) :=
      (fullEnergyPotentialPathLimit_ae_cadlag_and_uniform hwalkm hG hm' hmsum' start (U n)
        start).mono fun _ hω => hω.1
    have hvertN : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start), ∀ t x,
        (fastPF e D hG).X t ω = some x →
          fullEnergyPotentialPathLimit (decode e).graph (fastSpeed e D hG) hm'
              (fastPF e D hG) start (U n) t ω =
            unweight (fastSpeed e D hG)
                (valueInclusion (decode e).graph (fastSpeed e D hG) (U n)) x -
              unweight (fastSpeed e D hG)
                (valueInclusion (decode e).graph (fastSpeed e D hG) (U n)) start :=
      fullEnergyPotentialPathLimit_ae_eq_at_vertex_times hwalkm hG hm' hmsum' start (U n) start
    have hstartn : ‖lexMinField.at e start‖ ≤ R n / 2 := by
      have := hRmono (Nat.zero_le n)
      linarith
    -- the pathwise identification and bound
    have hpath : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
        (∀ t : ℝ≥0,
          stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting
              (areaPF e D hG) (region e (R n / 2)) ω}.indicator (fun ω => M t ω i))
            (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2))) t ω =
          unweight (fastSpeed e D hG)
              (valueInclusion (decode e).graph (fastSpeed e D hG) (U n)) start +
            stoppedValue (stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
                (fastSpeed e D hG) hm' (fastPF e D hG) start (U n))
              (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (R n / 2))))
              (fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t) ω) ∧
        ∀ q : ℝ≥0, |stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
            (fastSpeed e D hG) hm' (fastPF e D hG) start (U n))
          (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (R n / 2))) q ω| ≤
          2 * K' n := by
      filter_upwards [hgp, hpcc, hrcA, hentA, hedgeA, hdyA, h0A, hcadN, hvertN]
        with ω hgpω hpω hrcω hentω hedgeω hdyω h0ω hcadω hvertω
      obtain ⟨hgood, hpathω⟩ := hgpω
      obtain ⟨hcol, -, -, -, -, -, -, -, -, hreg⟩ := hpω
      have hXY : ∀ t, (areaPF e D hG).X t ω =
          (fastPF e D hG).X ((goodOrderIso hgood).symm t) ω := fun t =>
        (hpathω t).trans (congrArg (fun s => (fastPF e D hG).X s ω)
          (inverseAreaClock_eq_symm_of_good hgood t))
      have hτ : StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (R n / 2)) ω =
          WithTop.map (goodOrderIso hgood).symm
            (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2)) ω) :=
        CoordinateLocallySquareIntegrableLocalizer.exitHitting_eq_map_symm (areaPF e D hG)
          (fastPF e D hG) (region e (R n / 2)) ω ω (goodOrderIso hgood) hXY
      obtain ⟨ε, hε, hconst0⟩ := hrcω 0 ⟨start, h0ω⟩
      have hσpos : 0 < StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (R n / 2)) ω :=
        CoordinateLocallySquareIntegrableLocalizer.exitHitting_pos (areaPF e D hG)
          (region e (R n / 2)) ω hstartn h0ω hε hconst0
      have hpre : ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < StoppedFormAssociation.exitHitting
          (areaPF e D hG) (region e (R n / 2)) ω →
          ∀ v, (areaPF e D hG).X r ω = some v → ‖lexMinField.at e v‖ ≤ R n / 2 :=
        fun r hr v hv =>
          CoordinateLocallySquareIntegrableLocalizer.mem_of_lt_exitHitting (areaPF e D hG)
            (region e (R n / 2)) ω hr hv
      have hMv : ∀ t v, (areaPF e D hG).X t ω = some v → M t ω = (Φ.at e) v := by
        intro t v hv
        exact hreg.1.2.1 t v (inl_of_collapse_eq_some ((hcol t).trans hv))
      have hMn : ∀ t, (areaPF e D hG).X t ω = none → ContinuousAt (fun t => M t ω) t := by
        intro t hv
        obtain ⟨b, hb⟩ := exists_inr_of_collapse_eq_none ((hcol t).trans hv)
        exact hreg.1.2.2 t b hb
      have hu : ∀ v, ‖lexMinField.at e v‖ ≤ R n →
          unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) (U n)) v = (Φ.at e) v i :=
        fun v hv => hUeq n hv
      have hkey := CoordinateLocallySquareIntegrableExit.stoppedProcess_coord_eq hF hz
        (hRpos n) (hD n) (hzΦ n) (hΦA n) hrcω hentω hedgeω hdyω hMv hMn hσpos hpre i hu
        start (goodOrderIso hgood) hXY hreg.1.1 hcadω hvertω
      have hbound := CoordinateLocallySquareIntegrableExit.abs_stoppedProcess_le hF hz
        (hRpos n) (hD n) (hzΦ n) (hΦA n) hrcω hentω hedgeω hdyω hMv hMn hσpos hpre i hu
        start (goodOrderIso hgood) hXY hreg.1.1 hcadω hvertω (hΦB n) hstartn
      refine ⟨fun t => ?_, fun q => ?_⟩
      · have hfc : fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t ω =
            (((goodOrderIso hgood).symm t : ℝ≥0) : WithTop ℝ≥0) := by
          rw [fastClock_of_good hgood, inverseAreaClock_eq_symm_of_good hgood]
        have h1 := stoppedProcess_indicator_of_pos (X := fun t ω => M t ω i)
          (σ := StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2)))
          (ω := ω) hσpos t
        have h2 := stoppedValue_stoppedProcess_coe (N := fullEnergyPotentialPathLimit
            (decode e).graph (fastSpeed e D hG) hm' (fastPF e D hG) start (U n))
          (τ := StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (R n / 2))) hfc
        have h3 := congrArg (fun x => fullEnergyPotentialPathLimit (decode e).graph
          (fastSpeed e D hG) hm' (fastPF e D hG) start (U n)
          (min (((goodOrderIso hgood).symm t : ℝ≥0) : WithTop ℝ≥0) x).untopA ω) hτ
        exact h1.trans ((hkey t).trans
          (congrArg (fun x => unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) (U n)) start + x)
            (h2.trans h3).symm))
      · have h3 := congrArg (fun x => |fullEnergyPotentialPathLimit (decode e).graph
          (fastSpeed e D hG) hm' (fastPF e D hG) start (U n) (min (q : WithTop ℝ≥0) x).untopA ω|)
          hτ
        exact h3.le.trans (hbound q)
    have hr : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion,
        IsRightContinuous (fun t => stoppedProcess (fullEnergyPotentialPathLimit
          (decode e).graph (fastSpeed e D hG) hm' (fastPF e D hG) start (U n))
          (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (R n / 2))) t ω) := by
      refine StoppedFormAssociation.ae_completion_of_ae ?_
      filter_upwards [hcadN] with ω hω
      exact MartingaleLimit.isRightContinuous_stoppedProcess_common ω hω.isRightContinuous _
    exact martingale_memLp_of_clock (P := (areaSampleLaw (decode e) D hG start).completion)
      (G := areaFiltration e D (areaSampleLaw (decode e) D hG start)) hN hr
      (StoppedFormAssociation.ae_completion_of_ae (hpath.mono fun _ hω => hω.2))
      (isStoppingTime_fastClock_env e D hG hdat start)
      (fun ω => monotone_fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) ω)
      (fun t ω => fastClock_ne_top (decode e) (fastSpeed e D hG) (fastPF e D hG) t ω)
      (areaFiltration_ae_le_measurableSpace_fastClock e D hG hdat start) hnullG
      (hZadapt n) _
      (fun t => StoppedFormAssociation.ae_completion_of_ae (hpath.mono fun _ hω => hω.1 t))
  -- the localizing sequence
  have hloc : IsLocalizingSequence (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun n => StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2)))
      (areaSampleLaw (decode e) D hG start).completion :=
    { isStoppingTime := hσstop
      tendsto_top := by
        refine StoppedFormAssociation.ae_completion_of_ae ?_
        filter_upwards [hbdd] with ω hω
        refine CoordinateLocallySquareIntegrableLocalizer.tendsto_exitHitting_top
          (areaPF e D hG) (fun n => region e (R n / 2)) hAmono ω fun T => ?_
        obtain ⟨Mb, hMb⟩ := hω T
        obtain ⟨n, hn⟩ := hRtop (2 * Mb)
        refine ⟨n, fun t ht v hv => ?_⟩
        have h1 : ‖lexMinField.at e v‖ ≤ Mb := hMb t ht v hv
        show ‖lexMinField.at e v‖ ≤ R n / 2
        linarith
      mono := ae_of_all _ fun ω a b hab => by
        show StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R a / 2)) ω ≤
          StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R b / 2)) ω
        exact CoordinateLocallySquareIntegrableLocalizer.exitHitting_mono (areaPF e D hG)
          (hAmono hab) ω }
  exact ⟨hMadapt, _, hloc, hcore⟩

end Environment

/-! ## The ν-level producer -/

section Producer

/-- **Bracket atom 1, from the manuscript's hypotheses alone.**  Almost surely in the environment,
for every exhaustion, connectivity witness and start carrying the environment walk data, and every
pinned lift `M` satisfying the pathwise clock clauses, each coordinate of `M` is a locally
square-integrable martingale of the completed area filtration.  The inputs are `MassTransport ν`,
the (FE) moment and `IsHarmonicCoordinate ν Φ`. -/
theorem ae_coordinateLocallySquareIntegrable (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ) :
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          CoordinateLocallySquareIntegrable e D hG start M := by
  have hMax := SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity
    ν hmt hFE.ne
  filter_upwards [LocalHarmonicClockEnvironment.ae_exists_cutoff_and_hU_of_isHarmonicCoordinate
      ν hmt hFE Φ hΦ,
    AlmostSureCutoffBounds.ae_exists_diameter_bound ν hmt hFE.ne,
    AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hmt hFE.ne hMax,
    hΦ.2.2.2.2.1] with e hcutE hdiam hlog hΦe
  intro hnt D hG hdat start Xexp Xexact M hpcc
  letI := hnt
  obtain ⟨Rc, -, hcutR⟩ := hcutE
  obtain ⟨Rd, -, hdiamR⟩ := hdiam
  obtain ⟨Rs, -, hsub⟩ := hΦe.2.2.2.2.2 (lexMinField.at e) (isCellRepresentative_lexMinField e)
    (1 / 10) (by norm_num)
  obtain ⟨hmin, hrate, hwalkA, -⟩ := id hdat
  obtain ⟨r₀, C, hr₀, hC, ho, hD0, hW⟩ := hlog (lexMinField.at e) start
  have hbdd := LogCutoffSpatialBoundedness.reflected_ae_forall_bddAbove_norm_on_boundedTime
    (decode e) (decode_geometry e) (lexMinField.at e) (isCellRepresentative_lexMinField e)
    (areaPF e D hG) hwalkA hrate start hr₀ hC ho hD0 hW
  have hz : CellRepresentatives (decode e) (lexMinField.at e) :=
    isCellRepresentative_lexMinField e
  -- the radii
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = max (max Rc Rd) (max (2 * Rs)
      (max 6 (2 * ‖lexMinField.at e start‖))) := ⟨_, rfl⟩
  have hXc : Rc ≤ X := by rw [hXdef]; exact le_max_of_le_left (le_max_left _ _)
  have hXd : Rd ≤ X := by rw [hXdef]; exact le_max_of_le_left (le_max_right _ _)
  have hXs : 2 * Rs ≤ X := by rw [hXdef]; exact le_max_of_le_right (le_max_left _ _)
  have hX6 : 6 ≤ X := by
    rw [hXdef]; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hXo : 2 * ‖lexMinField.at e start‖ ≤ X := by
    rw [hXdef]; exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  -- the radii `Rf n = ⌈X⌉₊ + 1 + n`, kept opaque behind their defining equation
  obtain ⟨Rf, hRf⟩ : ∃ Rf : ℕ → ℝ, ∀ n, Rf n = ((⌈X⌉₊ + 1 + n : ℕ) : ℝ) :=
    ⟨fun n => ((⌈X⌉₊ + 1 + n : ℕ) : ℝ), fun _ => rfl⟩
  have hRge : ∀ n : ℕ, X ≤ Rf n := by
    intro n
    rw [hRf n]
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    have h2 : ((⌈X⌉₊ : ℕ) : ℝ) ≤ ((⌈X⌉₊ + 1 + n : ℕ) : ℝ) := by
      exact_mod_cast (by omega : ⌈X⌉₊ ≤ ⌈X⌉₊ + 1 + n)
    linarith
  obtain ⟨Kf, hKf⟩ : ∃ Kf : ℕ → ℝ, ∀ n, Kf n = Rf n / 2 + Rf n / 20 :=
    ⟨fun n => Rf n / 2 + Rf n / 20, fun _ => rfl⟩
  obtain ⟨Kf', hKf'⟩ : ∃ Kf' : ℕ → ℝ, ∀ n, Kf' n = Rf n + Rf n / 10 :=
    ⟨fun n => Rf n + Rf n / 10, fun _ => rfl⟩
  -- the sublinear comparison between `Φ` and the representatives
  have hsubv : ∀ (ρ : ℝ), Rs ≤ ρ → ∀ v : Vertex e.val, ‖lexMinField.at e v‖ ≤ ρ →
      ‖(Φ.at e) v - lexMinField.at e v‖ ≤ 1 / 10 * ρ := by
    intro ρ hρ v hv
    refine hsub ρ hρ v ⟨lexMinField.at e v, hz v, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  refine coordinateLocallySquareIntegrable_of_radii e D hG hdat Φ start Xexp Xexact M hpcc
    Rf (fun n => by have := hRge n; linarith)
    (fun a b hab => by
      rw [hRf a, hRf b]
      exact_mod_cast (by omega : ⌈X⌉₊ + 1 + a ≤ ⌈X⌉₊ + 1 + b))
    (fun b => ⟨⌈b⌉₊, by
      rw [hRf]
      have h1 : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
      have h2 : ((⌈b⌉₊ : ℕ) : ℝ) ≤ ((⌈X⌉₊ + 1 + ⌈b⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast (by omega : ⌈b⌉₊ ≤ ⌈X⌉₊ + 1 + ⌈b⌉₊)
      linarith⟩)
    (fun n v hv => hdiamR (Rf n) (by have := hRge n; linarith) v hv)
    Kf Kf' ?_ ?_ ?_ ?_ ?_ hbdd
  · -- `‖Φ‖ ≤ K + 2 ⟹ ‖z‖ ≤ R`
    intro n v hv
    rw [hKf n] at hv
    have hRn := hRge n
    by_cases hsmall : ‖lexMinField.at e v‖ ≤ Rs
    · linarith
    · push Not at hsmall
      have h1 := hsubv (‖lexMinField.at e v‖) hsmall.le v le_rfl
      have h2 := norm_sub_norm_le (lexMinField.at e v) ((Φ.at e) v)
      rw [norm_sub_rev] at h2
      linarith
  · -- `‖z‖ ≤ R/2 ⟹ ‖Φ‖ ≤ K`
    intro n v hv
    rw [hKf n]
    have hRn := hRge n
    have h1 := hsubv (Rf n / 2) (by linarith) v hv
    have h2 := norm_sub_norm_le ((Φ.at e) v) (lexMinField.at e v)
    linarith
  · -- `‖z‖ ≤ R ⟹ ‖Φ‖ ≤ K'`
    intro n v hv
    rw [hKf' n]
    have hRn := hRge n
    have h1 := hsubv (Rf n) (by linarith) v hv
    have h2 := norm_sub_norm_le ((Φ.at e) v) (lexMinField.at e v)
    linarith
  · -- the start lies in the first region
    have hR0 := hRge 0
    linarith
  · -- the step-(a) cutoffs
    intro i n
    have hRn := hRge n
    rw [hRf n] at hRn ⊢
    exact hcutR hnt D hG hdat i (⌈X⌉₊ + 1 + n) (by linarith)

end Producer

end ReflectedGMS.CoordinateLocallySquareIntegrableProof
