/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.DiagonalCompensatedSquares at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoordinateLocallySquareIntegrable
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedRemainderCompensatedSquare
import LatticeProb.Bonanno.ReflectedGMS.Forms.TimeChangedOccupation
import LatticeProb.Bonanno.ReflectedGMS.Limit.DiagonalCompensatedSquaresClock
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoordinateLocallySquareIntegrableExit

/-!
# Bracket atom 2 at one environment: one compensated square clause

`BracketClausesScalarReduction.CompensatedSquareClause e D hG start u Z`: the square of `Z`
compensated by the canonical area occupation of `u` is a local martingale of the completed area
filtration.  Here `Z = ℓ ∘ M` for a continuous `ℓ : Plane → ℝ` and `u = ℓ ∘ Φ` (for
`DiagonalCompensatedSquares`, `ℓ = (· i)` and `ℓ = (· i) + (· j)`).  The route is atom 1's
(`CoordinateLocallySquareIntegrable.coordinateLocallySquareIntegrable_of_radii`), with the SAME
localizer `σ_n` (area exit from `{‖z‖ ≤ R_n/2}`), the SAME clock `h = A⁻¹`, filtration inclusion
and exit identification, and the fast-clock compensated square
`StoppedRemainder.martingale_stopped_fullEnergyPath_compensatedSquare_exit_completed_of_bounded`
in place of the fast potential.

On the good event, with `c₁ = U(start)`, `P` the full-energy path of the cutoff `U` and `τ` the
fast exit:

* `ℓ(M_{t∧σ}) = c₁ + P^τ(h t)` — `DiagonalCompensatedSquaresExit.stoppedProcess_lin_eq`;
* `⟨u⟩^{area}_{t∧σ} = ⟨U⟩^{area}_{t∧σ}` — step (c),
  `TimeChangedOccupation.lintegral_stateVertexCarreDuChamp_congr_of_le_exit`;
* `⟨U⟩^{area}_{t∧σ} = ⟨U⟩^{fast}(A⁻¹(t∧σ)) = ⟨U⟩^{fast,τ}(h t)` — step (b),
  `TimeChangedOccupation.ae_adaptedJumpOccupation_inverseAreaClock_eq`;

so the localized area process is `c₁² + 2c₁ · P^τ(h t) + [(P^τ)² − ⟨U⟩^τ](h t)`, and the clock
change `DiagonalCompensatedSquaresClock.martingale_of_clock_two` applies (the compensated square
is dominated, not bounded).

**Bounded cutoffs.**  The stopped zero-energy engine needs its stopped-path bound under EVERY
start (`hPb : ∀ z, …`), which a cutoff bounded only on the region cannot give (a walk started
outside the region stops at once, at an arbitrary value of `U`).  The producer therefore
supplies globally bounded cutoffs (truncations, `Limit/DiagonalCompensatedSquaresProducer`); this
file takes the global bound as a hypothesis of `hcut`.
-/

-- Merged from `ReflectedGMS/Limit/DiagonalCompensatedSquaresExit.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_DiagonalCompensatedSquaresExit

/-!
# The exit identification of atom 1, for a continuous functional of the extension

`CoordinateLocallySquareIntegrableExit.stoppedProcess_coord_eq` identifies the coordinate
`M_{t∧σ} · i` of the spatial extension with `u(start) + N_{e⁻¹ t ∧ e⁻¹ σ}`.  Atom 2 needs the same
identification for the coordinate sums `M · i + M · j` (the polarization inputs of
`DiagonalCompensatedSquares`).  The proof is atom 1's verbatim — the right window
`exists_right_window` is reused — with the coordinate projection replaced by an arbitrary
continuous `ℓ : Plane → ℝ`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.DiagonalCompensatedSquaresExit

open StatementIngredients
open ReflectedGMS.SpatialExtensionConstruction ReflectedGMS.SpatialExtensionChainJumps
open ReflectedGMS.CoordinateLocallySquareIntegrableExit

universe u

/-- The stopped time `t ∧ σ`, untopped, lies below `σ`. -/
theorem coe_untopA_min_le (t : ℝ≥0) (σ : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) σ).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ σ := by
  have hne : min (t : WithTop ℝ≥0) σ ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t)).ne
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  exact min_le_right _ _

section Pathwise

variable {V : Type u} [Countable V] {F : IndexedCells V} (hF : Geometry F)
  {z : V → Plane} (hz : CellRepresentatives F z) {R : ℝ} (hR : 0 < R)
  (hD : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
    Metric.diam (F.cell v : Set Plane) ≤ R / 100)
  {Φ : V → Plane} {K : ℝ}
  (hzΦ : ∀ v, ‖Φ v‖ ≤ K + 2 → ‖z v‖ ≤ R)
  (hΦA : ∀ v, ‖z v‖ ≤ R / 2 → ‖Φ v‖ ≤ K)
  {X : ℝ≥0 → Option V}
  (hrc : ∀ t, (∃ x, X t = some x) → ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Ico t (t + ε), X s = X t)
  (hent : NoBoundaryEntrance X) (hedge : EdgeJumps F X)
  (hdy : ∀ s ∈ globalDyadicSupport, ∃ x, X s = some x)
  {M : ℝ≥0 → Plane} (hMv : ∀ t v, X t = some v → M t = Φ v)
  (hMn : ∀ t, X t = none → ContinuousAt M t)
  {σ : WithTop ℝ≥0} (hσpos : 0 < σ)
  (hpre : ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < σ → ∀ v, X r = some v → ‖z v‖ ≤ R / 2)

include hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre in
/-- **The functional identity up to and including the exit.**  For every `θ ≤ σ`,
`ℓ(M_θ) = u(start) + N_{e⁻¹ θ}`, where `u = ℓ ∘ Φ` on `{‖z‖ ≤ R}`. -/
theorem lin_eq_of_le_exit {ℓ : Plane → ℝ} (hℓ : Continuous ℓ) {u : V → ℝ}
    (hu : ∀ v, ‖z v‖ ≤ R → u v = ℓ (Φ v))
    (start : V) {Y : ℝ≥0 → Option V} (e : ℝ≥0 ≃o ℝ≥0) (hXY : ∀ t, X t = Y (e.symm t))
    (hMc : IsCadlag M) {N : ℝ≥0 → ℝ} (hNc : IsCadlag N)
    (hNv : ∀ q y, Y q = some y → N q = u y - u start)
    (θ : ℝ≥0) (hθ : (θ : WithTop ℝ≥0) ≤ σ) :
    ℓ (M θ) = u start + N (e.symm θ) := by
  obtain ⟨δ, hδ, hwin⟩ :=
    exists_right_window hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre θ hθ
  refine eq_at_of_rightContinuous_of_eqOn_dyadic (f := fun r => ℓ (M r))
    (g := fun r => u start + N (e.symm r)) (lt_add_of_pos_right θ hδ) ?_ ?_ ?_
  · exact hℓ.continuousAt.comp_continuousWithinAt (hMc.isRightContinuous θ)
  · refine continuousWithinAt_const.add ?_
    exact (hNc.isRightContinuous (e.symm θ)).comp e.symm.continuous.continuousWithinAt
      (fun r hr => e.symm.strictMono hr)
  · intro r hr hθr hrb
    obtain ⟨x, hx⟩ := hdy r hr
    have hzx := hwin r hθr hrb x hx
    have hY : Y (e.symm r) = some x := by rw [← hXY]; exact hx
    show ℓ (M r) = u start + N (e.symm r)
    rw [hMv r x hx, hNv _ x hY, hu x hzx]
    ring

include hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre in
/-- **The stopped functional identification.**  `ℓ` of the extension stopped at `σ` is `u(start)`
plus the full-energy path `N` stopped at the carried exit `e⁻¹ σ` and read at `e⁻¹ t`. -/
theorem stoppedProcess_lin_eq {ℓ : Plane → ℝ} (hℓ : Continuous ℓ) {u : V → ℝ}
    (hu : ∀ v, ‖z v‖ ≤ R → u v = ℓ (Φ v))
    (start : V) {Y : ℝ≥0 → Option V} (e : ℝ≥0 ≃o ℝ≥0) (hXY : ∀ t, X t = Y (e.symm t))
    (hMc : IsCadlag M) {N : ℝ≥0 → ℝ} (hNc : IsCadlag N)
    (hNv : ∀ q y, Y q = some y → N q = u y - u start) (t : ℝ≥0) :
    ℓ (M (min (t : WithTop ℝ≥0) σ).untopA) =
      u start + N (min ((e.symm t : ℝ≥0) : WithTop ℝ≥0) (WithTop.map e.symm σ)).untopA := by
  have hne : min (t : WithTop ℝ≥0) σ ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t)).ne
  rw [min_coe_symm_map, untopA_map_symm e hne]
  exact lin_eq_of_le_exit hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre hℓ hu
    start e hXY hMc hNc hNv _ (coe_untopA_min_le t σ)

end Pathwise

end ReflectedGMS.DiagonalCompensatedSquaresExit

end Merged_DiagonalCompensatedSquaresExit

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.DiagonalCompensatedSquaresProof

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open MartingaleIngredients ReflectedWalk FullNetworkForm
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.SpatialExtensionConstruction
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.BracketClausesScalarReduction
open ReflectedGMS.AreaFastClockStopping ReflectedGMS.AreaFastClockPath
open ReflectedGMS.AreaFastClockFiltration ReflectedGMS.AreaTimeChangeJumpLaw
open ReflectedGMS.CoordinateLocallySquareIntegrableProof

/-- **The localized compensated square is a martingale**, for one region `{‖z‖ ≤ r/2}` and one
globally bounded cutoff `U` of `u = ℓ ∘ Φ` at radius `r`. -/
theorem martingale_stopped_compensatedSquare_of_cutoff (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    {ℓ : Plane → ℝ} (hℓ : Continuous ℓ) {u : Vertex e.val → ℝ}
    (hu : ∀ v, u v = ℓ (Φ.at e v))
    (hMadapt : StronglyAdapted (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun t ω => ℓ (M t ω)))
    (hYadapt : StronglyAdapted (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun t ω => ℓ (M t ω) ^ 2 -
        adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω))
    (hAcont : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Continuous (fun t => adaptedJumpOccupation (areaPF e D hG) (decode e).graph
        (cellArea (decode e)) u t ω))
    {r : ℝ} (hr : 0 < r)
    (hD : ∀ v : Vertex e.val, Hits (decode e) (Metric.closedBall (0 : Plane) r) v →
      Metric.diam ((decode e).cell v : Set Plane) ≤ r / 100)
    {K : ℝ}
    (hzΦ : ∀ v : Vertex e.val, ‖Φ.at e v‖ ≤ K + 2 → ‖lexMinField.at e v‖ ≤ r)
    (hΦA : ∀ v : Vertex e.val, ‖lexMinField.at e v‖ ≤ r / 2 → ‖Φ.at e v‖ ≤ K)
    (hstart : ‖lexMinField.at e start‖ ≤ r / 2)
    (U : hilbertDomain (decode e).graph (fastSpeed e D hG)) {C : ℝ}
    (hUeq : Set.EqOn (unweight (fastSpeed e D hG)
        (valueInclusion (decode e).graph (fastSpeed e D hG) U)) u (region e r))
    (hUb : ∀ x, |unweight (fastSpeed e D hG)
        (valueInclusion (decode e).graph (fastSpeed e D hG) U) x| ≤ C)
    (hU : ∀ w : hilbertDomain (decode e).graph (fastSpeed e D hG),
      (∀ x ∉ region e (r / 2),
        unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) w) x = 0) →
      (decode e).graph.dirichletForm
        (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG) U))
        (unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) w)) = 0) :
    Martingale
      (stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (r / 2)) ω}.indicator (fun ω => ℓ (M t ω) ^ 2 -
            adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω))
        (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2))))
      (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (areaSampleLaw (decode e) D hG start).completion := by
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
  have hnullG : ∀ (t : ℝ≥0) (A : Set (NullMeasurableSpace (Existence.Sample (Vertex e.val))
      (areaSampleLaw (decode e) D hG start))),
      (areaSampleLaw (decode e) D hG start).completion A = 0 →
      MeasurableSet[areaFiltration e D (areaSampleLaw (decode e) D hG start) t] A :=
    fun t A hA => ProcessFiltration.measurableSet_completedNaturalFiltration_of_null _ _ _ t A hA
  -- the area exit is a stopping time of the area filtration
  have hσstop : IsStoppingTime (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2))) :=
    StoppedFormAssociation.isStoppingTime_completed_exitHitting (h := hwalkA') (z := start)
      (A := region e (r / 2)) (henc := observedState_injective e)
      (X' := fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
      (hX'e := fun _ _ => rfl)
      (hX' := fun t => (measurable_of_countable (observedState e)).comp
        (measurable_exponentialAreaPath (decode e) D t))
  have hposmeas : ∀ t : ℝ≥0,
      MeasurableSet[areaFiltration e D (areaSampleLaw (decode e) D hG start) t]
        {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2)) ω} := by
    intro t
    have h0 := hσstop 0
    have hc := (areaFiltration e D (areaSampleLaw (decode e) D hG start)).mono
      (show (0 : ℝ≥0) ≤ t from zero_le) _ h0.compl
    convert hc using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
    exact Iff.rfl
  -- the two localized area processes are adapted
  have hWadapt : StronglyAdapted (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (r / 2)) ω}.indicator (fun ω => ℓ (M t ω)))
        (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2)))) := by
    refine ProcessFiltration.stronglyAdapted_stoppedProcess_completedNaturalFiltration
      (areaSampleLaw (decode e) D hG start)
      (fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
      (fun t => (measurable_of_countable (observedState e)).comp
        (measurable_exponentialAreaPath (decode e) D t)) ?_ hσstop ?_
    · intro t
      exact (hMadapt t).indicator (hposmeas t)
    · refine StoppedFormAssociation.ae_completion_of_ae ?_
      filter_upwards [hpcc] with ω hpω
      obtain ⟨-, -, -, -, -, -, -, -, -, hreg⟩ := hpω
      intro t
      have hMr : ContinuousWithinAt (fun t => ℓ (M t ω)) (Ioi t) t :=
        hℓ.continuousAt.comp_continuousWithinAt (hreg.1.1.isRightContinuous t)
      by_cases hω : ω ∈ {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (r / 2)) ω}
      · exact hMr.congr (fun s _ => Set.indicator_of_mem hω (fun ω => ℓ (M s ω)))
          (Set.indicator_of_mem hω (fun ω => ℓ (M t ω)))
      · exact continuousWithinAt_const.congr
          (fun s _ => Set.indicator_of_notMem hω (fun ω => ℓ (M s ω)))
          (Set.indicator_of_notMem hω (fun ω => ℓ (M t ω)))
  have hZadapt : StronglyAdapted (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (r / 2)) ω}.indicator (fun ω => ℓ (M t ω) ^ 2 -
            adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω))
        (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2)))) := by
    refine ProcessFiltration.stronglyAdapted_stoppedProcess_completedNaturalFiltration
      (areaSampleLaw (decode e) D hG start)
      (fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
      (fun t => (measurable_of_countable (observedState e)).comp
        (measurable_exponentialAreaPath (decode e) D t)) ?_ hσstop ?_
    · intro t
      exact (hYadapt t).indicator (hposmeas t)
    · refine StoppedFormAssociation.ae_completion_of_ae ?_
      filter_upwards [hpcc, hAcont] with ω hpω hAω
      obtain ⟨-, -, -, -, -, -, -, -, -, hreg⟩ := hpω
      intro t
      have hYr : ContinuousWithinAt (fun t => ℓ (M t ω) ^ 2 -
          adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω)
          (Ioi t) t :=
        ((hℓ.continuousAt.comp_continuousWithinAt (hreg.1.1.isRightContinuous t)).pow 2).sub
          hAω.continuousAt.continuousWithinAt
      by_cases hω : ω ∈ {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (r / 2)) ω}
      · exact hYr.congr (fun s _ => Set.indicator_of_mem hω (fun ω => ℓ (M s ω) ^ 2 -
            adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u s ω))
          (Set.indicator_of_mem hω (fun ω => ℓ (M t ω) ^ 2 -
            adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω))
      · exact continuousWithinAt_const.congr
          (fun s _ => Set.indicator_of_notMem hω (fun ω => ℓ (M s ω) ^ 2 -
            adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u s ω))
          (Set.indicator_of_notMem hω (fun ω => ℓ (M t ω) ^ 2 -
            adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω))
  -- almost-sure path facts of the area walk
  have hrcA : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      ∀ t : ℝ≥0, (∃ x, (areaPF e D hG).X t ω = some x) →
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
  -- the two fast-clock martingales
  have hN1 := StoppedFormAssociation.martingale_stopped_fullEnergyPath_exit_completed
    (h := hwalkm) (hG := hG) (hm := hm') (hmsum := hmsum') (default := start) (z := start)
    (U := U) (A := region e (r / 2)) (henc := observedState_injective e)
    (X' := fun t ω => observedState e (Existence.process D (summableFastRate e D hG) t ω))
    (hX'e := fun _ _ => rfl)
    (hX' := fun t => (measurable_of_countable (observedState e)).comp
      (Existence.measurable_process D (summableFastRate e D hG) t))
    hU
  have hN2 :=
    StoppedRemainder.martingale_stopped_fullEnergyPath_compensatedSquare_exit_completed_of_bounded
      (h := hwalkm) (hG := hG) (hm := hm') (hmsum := hmsum') (default := start) (z := start)
      (U := U) (A := region e (r / 2)) (henc := observedState_injective e)
      (X' := fun t ω => observedState e (Existence.process D (summableFastRate e D hG) t ω))
      (hX'e := fun _ _ => rfl)
      (hX' := fun t => (measurable_of_countable (observedState e)).comp
        (Existence.measurable_process D (summableFastRate e D hG) t))
      hUb hU
  have hcadN : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      IsCadlag (fun t => fullEnergyPotentialPathLimit (decode e).graph (fastSpeed e D hG) hm'
        (fastPF e D hG) start U t ω) :=
    (fullEnergyPotentialPathLimit_ae_cadlag_and_uniform hwalkm hG hm' hmsum' start U
      start).mono fun _ hω => hω.1
  have hvertN : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      ∀ t x, (fastPF e D hG).X t ω = some x →
        fullEnergyPotentialPathLimit (decode e).graph (fastSpeed e D hG) hm'
            (fastPF e D hG) start U t ω =
          unweight (fastSpeed e D hG)
              (valueInclusion (decode e).graph (fastSpeed e D hG) U) x -
            unweight (fastSpeed e D hG)
              (valueInclusion (decode e).graph (fastSpeed e D hG) U) start :=
    fullEnergyPotentialPathLimit_ae_eq_at_vertex_times hwalkm hG hm' hmsum' start U start
  have hAf := adaptedJumpOccupation_ae_eq_all_continuous_monotone hwalkm hG hm' hmsum'
    (hilbertDomain_hasFiniteEnergy (decode e).graph (fastSpeed e D hG) U) start
  have hbnd := StoppedRemainder.stoppedPath_bound_of_bounded (h := hwalkm) (hG := hG)
    (hm := hm') (hmsum := hmsum') (default := start) (U := U) (A := region e (r / 2)) hUb start
  -- steps (b) and (c)
  have hTC := TimeChangedOccupation.ae_adaptedJumpOccupation_inverseAreaClock_eq e D hG hdat start
    (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG) U))
  have hrepU := TimeChangedOccupation.ae_measurable_path_and_adaptedJumpOccupation_eq hwalkA
    (cellArea (decode e))
    (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG) U)) start
  have hrepu := TimeChangedOccupation.ae_measurable_path_and_adaptedJumpOccupation_eq hwalkA
    (cellArea (decode e)) u start
  have hloc : ∀ v ∈ region e (r / 2),
      stateVertexCarreDuChamp (decode e).graph (cellArea (decode e))
          (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG) U))
          (some v) =
        stateVertexCarreDuChamp (decode e).graph (cellArea (decode e)) u (some v) := by
    intro v hv
    have hv' : ‖lexMinField.at e v‖ ≤ r / 2 := hv
    have hvr : ‖lexMinField.at e v‖ ≤ r := by linarith
    refine TimeChangedOccupation.stateVertexCarreDuChamp_some_congr _ _ (hUeq hvr)
      fun y hy => hUeq ?_
    exact LocalHarmonicClock.norm_le_of_adj hF hz hr hD hv' hy
  -- the pathwise identification
  have hpath : ∀ᵐ (ω : Existence.Sample (Vertex e.val)) ∂(areaSampleLaw (decode e) D hG start),
      (∀ t : ℝ≥0,
        stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
            (region e (r / 2)) ω}.indicator (fun ω => ℓ (M t ω)))
          (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2))) t ω =
        unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) U) start +
          stoppedValue (stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
              (fastSpeed e D hG) hm' (fastPF e D hG) start U)
            (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))))
            (fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t) ω) ∧
      (∀ t : ℝ≥0,
        stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
            (region e (r / 2)) ω}.indicator (fun ω => ℓ (M t ω) ^ 2 -
              adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e))
                u t ω))
          (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2))) t ω =
        unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) U) start ^ 2 +
          2 * unweight (fastSpeed e D hG)
            (valueInclusion (decode e).graph (fastSpeed e D hG) U) start *
            stoppedValue (stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
                (fastSpeed e D hG) hm' (fastPF e D hG) start U)
              (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))))
              (fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t) ω +
          stoppedValue (fun t ω =>
              (stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
                (fastSpeed e D hG) hm' (fastPF e D hG) start U)
                (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))) t ω) ^ 2 -
              stoppedProcess (adaptedJumpOccupation (fastPF e D hG) (decode e).graph
                  (fastSpeed e D hG)
                  (unweight (fastSpeed e D hG)
                    (valueInclusion (decode e).graph (fastSpeed e D hG) U)))
                (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))) t ω)
            (fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t) ω) := by
    filter_upwards [hgp, hpcc, hrcA, hentA, hedgeA, hdyA, h0A, hcadN, hvertN, hTC, hrepU, hrepu]
      with ω hgpω hpω hrcω hentω hedgeω hdyω h0ω hcadω hvertω hTCω hrepUω hrepuω
    obtain ⟨hgood, hpathω⟩ := hgpω
    obtain ⟨hcol, -, -, -, -, -, -, -, -, hreg⟩ := hpω
    have hXY : ∀ t, (areaPF e D hG).X t ω =
        (fastPF e D hG).X ((goodOrderIso hgood).symm t) ω := fun t =>
      (hpathω t).trans (congrArg (fun s => (fastPF e D hG).X s ω)
        (inverseAreaClock_eq_symm_of_good hgood t))
    have hτ : StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2)) ω =
        WithTop.map (goodOrderIso hgood).symm
          (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2)) ω) :=
      CoordinateLocallySquareIntegrableLocalizer.exitHitting_eq_map_symm (areaPF e D hG)
        (fastPF e D hG) (region e (r / 2)) ω ω (goodOrderIso hgood) hXY
    obtain ⟨ε, hε, hconst0⟩ := hrcω 0 ⟨start, h0ω⟩
    have hσpos : 0 < StoppedFormAssociation.exitHitting (areaPF e D hG)
        (region e (r / 2)) ω :=
      CoordinateLocallySquareIntegrableLocalizer.exitHitting_pos (areaPF e D hG)
        (region e (r / 2)) ω hstart h0ω hε hconst0
    have hpre : ∀ q : ℝ≥0, (q : WithTop ℝ≥0) < StoppedFormAssociation.exitHitting
        (areaPF e D hG) (region e (r / 2)) ω →
        ∀ v, (areaPF e D hG).X q ω = some v → ‖lexMinField.at e v‖ ≤ r / 2 :=
      fun q hq v hv =>
        CoordinateLocallySquareIntegrableLocalizer.mem_of_lt_exitHitting (areaPF e D hG)
          (region e (r / 2)) ω hq hv
    have hMv : ∀ t v, (areaPF e D hG).X t ω = some v → M t ω = (Φ.at e) v := by
      intro t v hv
      exact hreg.1.2.1 t v (inl_of_collapse_eq_some ((hcol t).trans hv))
    have hMn : ∀ t, (areaPF e D hG).X t ω = none → ContinuousAt (fun t => M t ω) t := by
      intro t hv
      obtain ⟨b, hb⟩ := exists_inr_of_collapse_eq_none ((hcol t).trans hv)
      exact hreg.1.2.2 t b hb
    have hu' : ∀ v, ‖lexMinField.at e v‖ ≤ r →
        unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) U) v = ℓ ((Φ.at e) v) :=
      fun v hv => (hUeq hv).trans (hu v)
    have hkey := DiagonalCompensatedSquaresExit.stoppedProcess_lin_eq hF hz hr hD hzΦ hΦA
      hrcω hentω hedgeω hdyω hMv hMn hσpos hpre hℓ hu' start (goodOrderIso hgood) hXY
      hreg.1.1 hcadω hvertω
    have hfc : ∀ t : ℝ≥0, fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t ω =
        (((goodOrderIso hgood).symm t : ℝ≥0) : WithTop ℝ≥0) := fun t => by
      rw [fastClock_of_good hgood, inverseAreaClock_eq_symm_of_good hgood]
    -- the occupation identity, steps (c) and (b)
    have hocc : ∀ t : ℝ≥0,
        adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u
            (min (t : WithTop ℝ≥0) (StoppedFormAssociation.exitHitting (areaPF e D hG)
              (region e (r / 2)) ω)).untopA ω =
          adaptedJumpOccupation (fastPF e D hG) (decode e).graph (fastSpeed e D hG)
            (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG) U))
            (min (((goodOrderIso hgood).symm t : ℝ≥0) : WithTop ℝ≥0)
              (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2)) ω)).untopA
            ω := by
      intro t
      have hθ := DiagonalCompensatedSquaresExit.coe_untopA_min_le t
        (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2)) ω)
      have hne : min (t : WithTop ℝ≥0) (StoppedFormAssociation.exitHitting (areaPF e D hG)
          (region e (r / 2)) ω) ≠ ⊤ :=
        (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t)).ne
      have hc : adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u
            (min (t : WithTop ℝ≥0) (StoppedFormAssociation.exitHitting (areaPF e D hG)
              (region e (r / 2)) ω)).untopA ω =
          adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e))
            (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG) U))
            (min (t : WithTop ℝ≥0) (StoppedFormAssociation.exitHitting (areaPF e D hG)
              (region e (r / 2)) ω)).untopA ω := by
        rw [hrepuω.2, hrepUω.2]
        congr 1
        exact (TimeChangedOccupation.lintegral_stateVertexCarreDuChamp_congr_of_le_exit
          (decode e).graph (cellArea (decode e)) (region e (r / 2)) hloc
          (fun q => (areaPF e D hG).X q ω) hpre _ hθ).symm
      rw [hc, ← hTCω, inverseAreaClock_eq_symm_of_good hgood, hτ,
        CoordinateLocallySquareIntegrableExit.min_coe_symm_map,
        CoordinateLocallySquareIntegrableExit.untopA_map_symm _ hne]
    refine ⟨fun t => ?_, fun t => ?_⟩
    · have h1 : stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting
            (areaPF e D hG) (region e (r / 2)) ω}.indicator (fun ω => ℓ (M t ω)))
            (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2))) t ω =
          ℓ (M (min (t : WithTop ℝ≥0) (StoppedFormAssociation.exitHitting (areaPF e D hG)
            (region e (r / 2)) ω)).untopA ω) :=
        stoppedProcess_indicator_of_pos (X := fun t ω => ℓ (M t ω)) hσpos t
      have h2 : stoppedValue (stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
              (fastSpeed e D hG) hm' (fastPF e D hG) start U)
            (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))))
            (fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t) ω =
          fullEnergyPotentialPathLimit (decode e).graph (fastSpeed e D hG) hm' (fastPF e D hG)
            start U (min (((goodOrderIso hgood).symm t : ℝ≥0) : WithTop ℝ≥0)
              (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2)) ω)).untopA
            ω :=
        stoppedValue_stoppedProcess_coe (hfc t)
      rw [h1, h2, hτ]
      exact hkey t
    · have h1 : stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting
            (areaPF e D hG) (region e (r / 2)) ω}.indicator (fun ω => ℓ (M t ω) ^ 2 -
              adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e))
                u t ω))
            (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (r / 2))) t ω =
          ℓ (M (min (t : WithTop ℝ≥0) (StoppedFormAssociation.exitHitting (areaPF e D hG)
            (region e (r / 2)) ω)).untopA ω) ^ 2 -
          adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u
            (min (t : WithTop ℝ≥0) (StoppedFormAssociation.exitHitting (areaPF e D hG)
              (region e (r / 2)) ω)).untopA ω :=
        stoppedProcess_indicator_of_pos (X := fun t ω => ℓ (M t ω) ^ 2 -
          adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω)
          hσpos t
      have h2 : stoppedValue (stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
              (fastSpeed e D hG) hm' (fastPF e D hG) start U)
            (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))))
            (fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t) ω =
          fullEnergyPotentialPathLimit (decode e).graph (fastSpeed e D hG) hm' (fastPF e D hG)
            start U (min (((goodOrderIso hgood).symm t : ℝ≥0) : WithTop ℝ≥0)
              (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2)) ω)).untopA
            ω :=
        stoppedValue_stoppedProcess_coe (hfc t)
      have h3 : stoppedValue (fun t ω =>
              (stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
                (fastSpeed e D hG) hm' (fastPF e D hG) start U)
                (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))) t ω) ^ 2 -
              stoppedProcess (adaptedJumpOccupation (fastPF e D hG) (decode e).graph
                  (fastSpeed e D hG)
                  (unweight (fastSpeed e D hG)
                    (valueInclusion (decode e).graph (fastSpeed e D hG) U)))
                (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))) t ω)
            (fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) t) ω =
          (fullEnergyPotentialPathLimit (decode e).graph (fastSpeed e D hG) hm' (fastPF e D hG)
            start U (min (((goodOrderIso hgood).symm t : ℝ≥0) : WithTop ℝ≥0)
              (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2)) ω)).untopA
            ω) ^ 2 -
          adaptedJumpOccupation (fastPF e D hG) (decode e).graph (fastSpeed e D hG)
            (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG) U))
            (min (((goodOrderIso hgood).symm t : ℝ≥0) : WithTop ℝ≥0)
              (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2)) ω)).untopA
            ω := by
        unfold stoppedValue
        rw [hfc t]
        rfl
      have hk := hkey t
      rw [← hτ] at hk
      rw [h1, h2, h3, hk, hocc t]
      ring
  -- right continuity of the two fast martingales
  have hr1 : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion,
      IsRightContinuous (fun t => stoppedProcess (fullEnergyPotentialPathLimit
        (decode e).graph (fastSpeed e D hG) hm' (fastPF e D hG) start U)
        (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))) t ω) := by
    refine StoppedFormAssociation.ae_completion_of_ae ?_
    filter_upwards [hcadN] with ω hω
    exact MartingaleLimit.isRightContinuous_stoppedProcess_common ω hω.isRightContinuous _
  have hr2 : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start).completion,
      IsRightContinuous (fun t =>
        (stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
          (fastSpeed e D hG) hm' (fastPF e D hG) start U)
          (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))) t ω) ^ 2 -
        stoppedProcess (adaptedJumpOccupation (fastPF e D hG) (decode e).graph
            (fastSpeed e D hG)
            (unweight (fastSpeed e D hG)
              (valueInclusion (decode e).graph (fastSpeed e D hG) U)))
          (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))) t ω) := by
    refine StoppedFormAssociation.ae_completion_of_ae ?_
    filter_upwards [hcadN, hAf] with ω hω hAω
    have h1 := MartingaleLimit.isRightContinuous_stoppedProcess_common ω hω.isRightContinuous
      (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2)))
    have h2 := MartingaleLimit.isRightContinuous_stoppedProcess_common
      (M := adaptedJumpOccupation (fastPF e D hG) (decode e).graph (fastSpeed e D hG)
        (unweight (fastSpeed e D hG) (valueInclusion (decode e).graph (fastSpeed e D hG) U)))
      ω (fun a => hAω.2.1.continuousAt.continuousWithinAt)
      (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2)))
    intro a
    exact ((h1 a).pow 2).sub (h2 a)
  -- the domination of the compensated square
  obtain ⟨g, hg, hgd⟩ :=
    DiagonalCompensatedSquaresClock.exists_integrable_dom_of_compensatedSquare
      (P := (areaSampleLaw (decode e) D hG start).completion)
      (X := stoppedProcess (fullEnergyPotentialPathLimit (decode e).graph
          (fastSpeed e D hG) hm' (fastPF e D hG) start U)
        (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))))
      (A := stoppedProcess (adaptedJumpOccupation (fastPF e D hG) (decode e).graph
            (fastSpeed e D hG)
            (unweight (fastSpeed e D hG)
              (valueInclusion (decode e).graph (fastSpeed e D hG) U)))
          (StoppedFormAssociation.exitHitting (fastPF e D hG) (region e (r / 2))))
      hN2 (fun t => (hN1.integrable t).aestronglyMeasurable)
      (StoppedFormAssociation.ae_completion_of_ae hbnd)
      (fun ω => (DiagonalCompensatedSquaresClock.stoppedProcess_zero _ _ ω).trans
        (adaptedJumpOccupation_zero _ _ _ _ _))
      (fun t ω => by
        simp only [stoppedProcess]
        exact adaptedJumpOccupation_nonneg _ _ _ _ _ _)
      (StoppedFormAssociation.ae_completion_of_ae (hAf.mono fun _ hω =>
        DiagonalCompensatedSquaresClock.monotone_stoppedProcess hω.2.2))
  exact DiagonalCompensatedSquaresClock.martingale_of_clock_two
    (P := (areaSampleLaw (decode e) D hG start).completion)
    (G := areaFiltration e D (areaSampleLaw (decode e) D hG start))
    hN1 hr1 (StoppedFormAssociation.ae_completion_of_ae hbnd) hN2 hr2 hg hgd
    (isStoppingTime_fastClock_env e D hG hdat start)
    (fun ω => monotone_fastClock (decode e) (fastSpeed e D hG) (fastPF e D hG) ω)
    (fun t ω => fastClock_ne_top (decode e) (fastSpeed e D hG) (fastPF e D hG) t ω)
    (areaFiltration_ae_le_measurableSpace_fastClock e D hG hdat start) hnullG hWadapt hZadapt
    _ _ _
    (fun t => StoppedFormAssociation.ae_completion_of_ae (hpath.mono fun _ hω => hω.1 t))
    (fun t => StoppedFormAssociation.ae_completion_of_ae (hpath.mono fun _ hω => hω.2 t))

/-- **One compensated square clause at one environment, from explicit radii.**  The inputs are
atom 1's (`coordinateLocallySquareIntegrable_of_radii`), except that the cutoffs are asked
globally bounded, the local occupation finiteness `hfin` of `u` is added (it gives the continuity
of the area occupation), and `ℓ` is any continuous functional with `u = ℓ ∘ Φ`. -/
theorem compensatedSquareClause_of_radii (e : Env) [Nontrivial (Vertex e.val)]
    (D : (decode e).graph.Exhaustion) (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) (Φ : CellField) (start : Vertex e.val)
    (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
    (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane)
    (hpcc : PathwiseClockClauses e D hG Φ start Xexp Xexact M)
    {ℓ : Plane → ℝ} (hℓ : Continuous ℓ) {u : Vertex e.val → ℝ}
    (hu : ∀ v, u v = ℓ (Φ.at e v))
    (hfin : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start), ∀ t : ℝ≥0,
      stationaryJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω < ∞)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hRmono : Monotone R)
    (hRtop : ∀ b : ℝ, ∃ n, b ≤ R n)
    (hD : ∀ (n : ℕ) (v : Vertex e.val),
      Hits (decode e) (Metric.closedBall (0 : Plane) (R n)) v →
        Metric.diam ((decode e).cell v : Set Plane) ≤ R n / 100)
    (K : ℕ → ℝ)
    (hzΦ : ∀ (n : ℕ) (v : Vertex e.val), ‖Φ.at e v‖ ≤ K n + 2 → ‖lexMinField.at e v‖ ≤ R n)
    (hΦA : ∀ (n : ℕ) (v : Vertex e.val), ‖lexMinField.at e v‖ ≤ R n / 2 → ‖Φ.at e v‖ ≤ K n)
    (hstart : ‖lexMinField.at e start‖ ≤ R 0 / 2)
    (hcut : ∀ n : ℕ, ∃ U : hilbertDomain (decode e).graph (fastSpeed e D hG), ∃ C : ℝ,
      Set.EqOn (unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) U)) u (region e (R n)) ∧
      (∀ x, |unweight (fastSpeed e D hG)
          (valueInclusion (decode e).graph (fastSpeed e D hG) U) x| ≤ C) ∧
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
    CompensatedSquareClause e D hG start u (fun t ω => ℓ (M t ω)) := by
  obtain ⟨hmin, hrate, hwalkA, -⟩ := id hdat
  haveI : IsFiniteMeasure (areaSampleLaw (decode e) D hG start).completion :=
    isFiniteMeasure_areaSampleLaw_completion e D hG start
  have hwalkA' : IsReflectedWalk (decode e).graph
      (fun v => (decode e).graph.pi v / cellArea (decode e) v) hmin (areaPF e D hG) := hwalkA
  choose U C hUeq hUb hU using hcut
  have hnullG : ∀ (t : ℝ≥0) (A : Set (NullMeasurableSpace (Existence.Sample (Vertex e.val))
      (areaSampleLaw (decode e) D hG start))),
      (areaSampleLaw (decode e) D hG start).completion A = 0 →
      MeasurableSet[areaFiltration e D (areaSampleLaw (decode e) D hG start) t] A :=
    fun t A hA => ProcessFiltration.measurableSet_completedNaturalFiltration_of_null _ _ _ t A hA
  -- `ℓ ∘ M` is adapted
  have hMadapt : StronglyAdapted (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun t ω => ℓ (M t ω)) := by
    intro t
    let g : ℕ → ℝ := fun k =>
      match (Encodable.decode k : Option (Option (Vertex e.val))) with
      | some (some v) => ℓ ((Φ.at e) v)
      | _ => 0
    have hg : ∀ v : Vertex e.val, g (Encodable.encode (some v)) = ℓ ((Φ.at e) v) := by
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
    show g (observedState e (exponentialAreaPath (decode e) D t ω)) = ℓ (M t ω)
    rw [hx, hMx]
    exact hg x
  -- the area occupation of `u` is adapted and continuous
  have hAadapt : StronglyAdapted (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun t ω => adaptedJumpOccupation (areaPF e D hG) (decode e).graph
        (cellArea (decode e)) u t ω) := by
    intro t
    exact (stronglyAdapted_adaptedJumpOccupation (areaPF e D hG) (decode e).graph
      (cellArea (decode e)) u t).mono
      (((areaPF e D hG).naturalFiltration.le_rightCont t).trans
        (StoppedFormAssociation.rightCont_naturalFiltration_le_completedNaturalFiltration
          (areaSampleLaw (decode e) D hG start) (observedState_injective e)
          (areaPF e D hG).X (areaPF e D hG).measurable_X
          (fun t ω => observedState e (exponentialAreaPath (decode e) D t ω))
          (fun _ _ => rfl)
          (fun t => (measurable_of_countable (observedState e)).comp
            (measurable_exponentialAreaPath (decode e) D t)) t))
  have hYadapt : StronglyAdapted (areaFiltration e D (areaSampleLaw (decode e) D hG start))
      (fun t ω => ℓ (M t ω) ^ 2 -
        adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e)) u t ω) :=
    fun t => ((hMadapt t).pow 2).sub (hAadapt t)
  have hAcont : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      Continuous (fun t => adaptedJumpOccupation (areaPF e D hG) (decode e).graph
        (cellArea (decode e)) u t ω) :=
    (LocalizedBracketRegularity.adaptedJumpOccupation_ae_zero_continuous_boundedVariation_of_ae_lt_top
      (hmin := hmin) hwalkA' u start hfin).mono fun _ hω => hω.2.1
  -- the localizing sequence: exits of the area path (atom 1's)
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
  have hcore : ∀ n : ℕ,
      Martingale
        (stoppedProcess (fun t => {ω | ⊥ < StoppedFormAssociation.exitHitting (areaPF e D hG)
            (region e (R n / 2)) ω}.indicator (fun ω => ℓ (M t ω) ^ 2 -
              adaptedJumpOccupation (areaPF e D hG) (decode e).graph (cellArea (decode e))
                u t ω))
          (StoppedFormAssociation.exitHitting (areaPF e D hG) (region e (R n / 2))))
        (areaFiltration e D (areaSampleLaw (decode e) D hG start))
        (areaSampleLaw (decode e) D hG start).completion := by
    intro n
    have hstartn : ‖lexMinField.at e start‖ ≤ R n / 2 := by
      have := hRmono (Nat.zero_le n)
      linarith
    exact martingale_stopped_compensatedSquare_of_cutoff e D hG hdat Φ start Xexp Xexact M hpcc
      hℓ hu hMadapt hYadapt hAcont (hRpos n) (hD n) (hzΦ n) (hΦA n) hstartn (U n) (hUeq n)
      (hUb n) (hU n)
  exact ⟨hYadapt, _, hloc, hcore⟩

end ReflectedGMS.DiagonalCompensatedSquaresProof
