/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.AlmostSureCutoffBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.LogCutoffSpatialBoundedness
import LatticeProb.Bonanno.ReflectedGMS.Spatial.LargeCellDiameterDecay

/-!
# The logarithmic cutoff hypotheses for the actual random environment

`Recurrence/LogCutoffSpatialBoundedness.lean` proves the manuscript's spatial boundedness
and end-avoidance conclusions for the actual reflected walk *from two deterministic
environment hypotheses*:

* `hD` — for every radius `R ≥ r₀`, every cell meeting `B̄_R` has diameter at most `R/100`;
* `hW` — for every radius `R ≥ r₀`, the diameter-weighted conductance mass
  `LogCutoff.localMassENN F {v | Hits F B̄_R v} = ∑_{H ∩ B̄_R ≠ ∅} d_H² π_H` is at most
  `C R²`.

Neither holds with a *deterministic uniform* `r₀`, `C` for the actual Gwynne–Miller–Sheffield
environment: both radii are random.  This file produces them with a **random finite starting
radius and constant**, preserving every radius `R ≥ r₀`.

## What is proved unconditionally here

`hD` is *removed as a hypothesis*.  It is exactly the `ε = 1/100` instance of the checked
large-cell decay `Spatial.maxDiamHittingBall_sublinear`, whose almost-sure form
`Spatial.ae_maxDiamHittingBall_finite_and_sublinear` needs only mass transport and the
manuscript's finite (FE) moment.  `exists_diameter_bound_of_maxDiamHittingBall_sublinear`
is the deterministic step; no cell is replaced by a centroid and no uniform bound is assumed.

`hW` is *reduced to a Lebesgue ball average of the rooted (FE) density*, which is what the
spatial maximal inequality controls.  The reduction is the actual mass-density geometry of
`Spatial/RootedMassBounds.lean`:

* `tsum_cellDensity_le_setLIntegral` — the cells of `A` have pairwise disjoint interiors and
  Lebesgue-null frontiers, and `RootDensities.rootAt` picks out exactly one of them at almost
  every point, so `∑_{H ∈ A} a_H g(H) ≤ ∫_B g(H_z) dz` whenever every cell of `A` lies in `B`.
  This is the same cellwise-to-integral transfer that `Corrector/SpecificEnergyLocalControl`
  performs for the specific-energy density, stated once for an arbitrary vertex density `g`.
* `ofReal_diamSq_mul_pi_le_volume_mul_finiteEnergyDensity` — the manuscript's (FE) integrand
  `(d_H²/a_H)(π_H + π*_H)` dominates `d_H² π_H / a_H`, because `π*_H ≥ 0`
  (`Spatial.piStar_nonneg`).  So the local mass of `A` is below the (FE) density integral.
* `localMassENN_hittingBall_le_of_ballBound` — a cell meeting `B̄_R` of diameter at most
  `R/100` lies in `B̄_{R+R/100}`, and `(R + R/100)² ≤ 2 R²`, so a ball bound
  `∫_{B̄_r} ρ_FE ≤ r² M` gives `hW` with the explicit constant `C = 2 M`.

`exists_logCutoff_hypotheses` assembles both into the exact hypothesis tuple of
`LogCutoff.cutoff_energy_le` and `LogCutoffSpatialBoundedness`, with `r₀ = max R₀ ‖z o‖`, and
`ae_exists_logCutoff_hypotheses` is its almost-sure environment form.  The compact-time
spatial boundedness and the end-avoidance corollaries are then composed.

## The input that is *not* proved here

The ball bound `∫_{B̄_r} ρ_FE ≤ r² M` with `M < ∞` is the manuscript's spatial maximal
inequality `s:prop:maximal`, in exactly the shape produced by
`ReflectedGMS.SpatialMaximalInequality.ballAverage_le_ballMaximal` together with
`ballMaximal_lt_top_ae`.  That module still carries its own explicit `BlockData` /
`OriginChainRegular` / `EnvironmentGrid` producers (the marked block transport), and the
identification of its density with `RootDensities.rootedFiniteEnergyDensity` is not made
here.  It is a quantitative statement about Lebesgue averages of a rooted density, a
different object from the vertex-indexed conductance mass `localMassENN` that it is used to
bound; it is not a disguised form of any conclusion below.  Nothing in this file claims the
recurrence theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.AlmostSureCutoffBounds

open ReflectedWalk Code EnvironmentLaws

universe u

section Deterministic

variable {V : Type u} [Countable V]

/-! ### The cellwise sum of a vertex density is below its rooted integral -/

/-- **Cellwise mass to Lebesgue integral, for an arbitrary vertex density.**  If every cell
of `A` is contained in `B`, then `∑_{H ∈ A} a_H g(H) ≤ ∫_B g(H_z) dz`, where `H_z` is the
boundary-masked root `RootDensities.rootAt`.

The three geometric facts used are exactly the `Geometry` clauses: distinct cells have
disjoint interiors, every cell frontier is Lebesgue null (so the global boundary mask is
null and the interior carries the full area), and the interior root is unique off the mask.
This is the density-independent form of the transfer already performed for the
specific-energy density in `Corrector/SpecificEnergyLocalControl`. -/
theorem tsum_cellDensity_le_setLIntegral (F : IndexedCells V) (hF : Geometry F)
    (g : V → ℝ≥0∞) {A : Set V} {B : Set Plane}
    (hAB : ∀ v ∈ A, (F.cell v : Set Plane) ⊆ B) :
    (∑' v : A, volume ((F.cell v.1 : Set Plane)) * g v.1)
      ≤ ∫⁻ z in B, (RootDensities.rootAt F z).elim 0 g ∂volume := by
  classical
  have hmask : volume (RootDensities.boundaryMask F) = 0 := by
    -- The mask is the frontier union together with the uncovered set; both are Lebesgue-null,
    -- the second by the covering clause of `Geometry`.
    show volume ((⋃ v : V, frontier (F.cell v : Set Plane)) ∪ uncoveredSet F) = 0
    exact measure_union_null (measure_iUnion_null fun v => hF.2.2.1 v) (volume_uncoveredSet hF)
  have hmeasInt : ∀ v : V, MeasurableSet (interior (F.cell v : Set Plane)) :=
    fun v => isOpen_interior.measurableSet
  have hterm : ∀ v : A,
      (∫⁻ z in B, Set.indicator (interior (F.cell v.1 : Set Plane))
          (fun _ => g v.1) z ∂volume)
        = volume ((F.cell v.1 : Set Plane)) * g v.1 := by
    intro v
    rw [lintegral_indicator_const (hmeasInt v.1), Measure.restrict_apply (hmeasInt v.1),
      Set.inter_eq_self_of_subset_left (subset_trans interior_subset (hAB v.1 v.2)),
      ReflectedGMS.Spatial.volume_interior_eq_of_frontier_null (hF.2.2.1 v.1)]
    exact mul_comm _ _
  have hsum : (∑' v : A, volume ((F.cell v.1 : Set Plane)) * g v.1)
      = ∫⁻ z in B, ∑' v : A, Set.indicator (interior (F.cell v.1 : Set Plane))
          (fun _ => g v.1) z ∂volume := by
    rw [lintegral_tsum fun v : A =>
      ((measurable_const.indicator (hmeasInt v.1)).aemeasurable)]
    exact (tsum_congr hterm).symm
  rw [hsum]
  refine lintegral_mono_ae ?_
  have hae : ∀ᵐ z ∂(volume.restrict B), z ∉ RootDensities.boundaryMask F := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simpa using hmask
  filter_upwards [hae] with z hz
  by_cases hex : ∃ v : A, z ∈ interior (F.cell v.1 : Set Plane)
  · obtain ⟨v₀, hv₀⟩ := hex
    have hsingle : (∑' v : A, Set.indicator (interior (F.cell v.1 : Set Plane))
        (fun _ => g v.1) z) = g v₀.1 := by
      refine (tsum_eq_single v₀ ?_).trans (Set.indicator_of_mem hv₀ _)
      intro b hb
      refine Set.indicator_of_notMem (fun hbz => ?_) _
      have hne : b.1 ≠ v₀.1 := fun h => hb (Subtype.ext h)
      exact (Set.disjoint_left.1 (hF.2.2.2.1 hne) hbz) hv₀
    rw [hsingle]
    have hroot : RootDensities.rootAt F z = some v₀.1 :=
      (RootDensities.rootAt_eq_some_iff F hF z v₀.1).2 ⟨hz, hv₀⟩
    rw [hroot]
    exact le_rfl
  · push_neg at hex
    have hzero : ∀ v : A, Set.indicator (interior (F.cell v.1 : Set Plane))
        (fun _ => g v.1) z = 0 :=
      fun v => Set.indicator_of_notMem (hex v) _
    simp only [hzero, tsum_zero]
    exact zero_le

/-! ### The local mass is below the rooted (FE) density integral -/

/-- One cell's local mass `d_H² π_H` is below `a_H` times the manuscript's (FE) integrand
`(d_H²/a_H)(π_H + π*_H)`: the areas cancel and `π*_H ≥ 0`. -/
theorem ofReal_diamSq_mul_pi_le_volume_mul_finiteEnergyDensity
    (F : IndexedCells V) (hF : Geometry F) (v : V) :
    ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2 * F.graph.pi v)
      ≤ volume ((F.cell v : Set Plane)) * RootDensities.finiteEnergyDensity F v := by
  have hvol := cellVolume_pos_lt_top F hF v
  have hA : volume ((F.cell v : Set Plane))
      = ENNReal.ofReal (StatementIngredients.cellArea F v) :=
    (ENNReal.ofReal_toReal hvol.2.ne).symm
  have hne0 : ENNReal.ofReal (StatementIngredients.cellArea F v) ≠ 0 := fun h =>
    absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 (StatementIngredients.cellArea_pos F hF v))
  have hnet : ENNReal.ofReal (StatementIngredients.cellArea F v) ≠ ∞ := ENNReal.ofReal_ne_top
  have hkey : volume ((F.cell v : Set Plane)) * RootDensities.finiteEnergyDensity F v
      = ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
          (ENNReal.ofReal (RootDensities.pi F v) +
            ENNReal.ofReal (RootDensities.piStar F v)) := by
    rw [hA]
    unfold RootDensities.finiteEnergyDensity
    rw [div_eq_mul_inv,
      show ENNReal.ofReal (StatementIngredients.cellArea F v) *
          (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ *
            (ENNReal.ofReal (RootDensities.pi F v) +
              ENNReal.ofReal (RootDensities.piStar F v)))
        = (ENNReal.ofReal (StatementIngredients.cellArea F v) *
              (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹) *
            (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              (ENNReal.ofReal (RootDensities.pi F v) +
                ENNReal.ofReal (RootDensities.piStar F v))) from by ring,
      ENNReal.mul_inv_cancel hne0 hnet, one_mul]
  rw [hkey, ENNReal.ofReal_mul (sq_nonneg _)]
  have hpi : ENNReal.ofReal (F.graph.pi v) = ENNReal.ofReal (RootDensities.pi F v) := rfl
  rw [hpi]
  exact mul_le_mul' le_rfl le_self_add

/-- The local mass as an indicator series over the whole vertex type. -/
theorem localMassENN_eq_tsum_indicator (F : IndexedCells V) (A : Set V) :
    LogCutoff.localMassENN F A
      = ∑' v : V, Set.indicator A
          (fun v => ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2 * F.graph.pi v)) v := by
  classical
  unfold LogCutoff.localMassENN
  refine tsum_congr fun v => ?_
  by_cases hv : v ∈ A <;> simp [hv]

/-- **The local mass comparison.**  If every cell meeting `A` lies in `B`, the manuscript's
diameter-weighted conductance mass of `A` is at most the Lebesgue integral over `B` of the
rooted (FE) density `ρ_FE(z) = (d_{H_z}²/a_{H_z})(π_{H_z} + π*_{H_z})`. -/
theorem localMassENN_le_setLIntegral_rootedFiniteEnergyDensity
    (F : IndexedCells V) (hF : Geometry F) {A : Set V} {B : Set Plane}
    (hAB : ∀ v ∈ A, (F.cell v : Set Plane) ⊆ B) :
    LogCutoff.localMassENN F A
      ≤ ∫⁻ z in B, RootDensities.rootedFiniteEnergyDensity F z ∂volume := by
  classical
  have hgen := tsum_cellDensity_le_setLIntegral F hF (RootDensities.finiteEnergyDensity F) hAB
  have hsplit : (∑' v : V, Set.indicator A
        (fun v => ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2 * F.graph.pi v)) v)
      ≤ ∑' v : V, Set.indicator A
        (fun v => volume ((F.cell v : Set Plane)) * RootDensities.finiteEnergyDensity F v) v := by
    refine ENNReal.tsum_le_tsum fun v => ?_
    by_cases hv : v ∈ A
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
      exact ofReal_diamSq_mul_pi_le_volume_mul_finiteEnergyDensity F hF v
    · rw [Set.indicator_of_notMem hv]
      exact zero_le
  have hsub := (tsum_subtype A
      (fun v => volume ((F.cell v : Set Plane)) * RootDensities.finiteEnergyDensity F v)).symm
  calc LogCutoff.localMassENN F A
      = _ := localMassENN_eq_tsum_indicator F A
    _ ≤ _ := hsplit
    _ = _ := hsub
    _ ≤ _ := hgen

/-! ### The two random-radius hypotheses -/

/-- A cell meeting `B̄_R` whose diameter is at most `DR` is contained in `B̄_{R+DR}`. -/
theorem cell_subset_closedBall_of_hits_of_diam_le (F : IndexedCells V) {R DR : ℝ} {v : V}
    (hv : Hits F (Metric.closedBall (0 : Plane) R) v)
    (hd : Metric.diam (F.cell v : Set Plane) ≤ DR) :
    (F.cell v : Set Plane) ⊆ Metric.closedBall (0 : Plane) (R + DR) := by
  obtain ⟨y, hyc, hyB⟩ := hv
  intro x hx
  have hdist : dist x y ≤ Metric.diam (F.cell v : Set Plane) :=
    Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded hx hyc
  rw [Metric.mem_closedBall] at hyB ⊢
  calc dist x 0 ≤ dist x y + dist y 0 := dist_triangle _ _ _
    _ ≤ DR + R := add_le_add (le_trans hdist hd) hyB
    _ = R + DR := by ring

/-- **`hW` from a ball bound on the rooted (FE) density.**  Given the local diameter bound
at every radius `R ≥ r₀` and a finite maximal constant `M` for the Lebesgue ball averages of
`ρ_FE`, the manuscript's quadratic local-mass bound holds for every `R ≥ r₀` with the
explicit constant `C = 2 M`. -/
theorem localMassENN_hittingBall_le_of_ballBound
    (F : IndexedCells V) (hF : Geometry F) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    {M : ℝ≥0∞} (hMtop : M ≠ ∞)
    (hM : ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity F x ∂volume) ≤ ENNReal.ofReal (r ^ 2) * M) :
    ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v}
        ≤ ENNReal.ofReal (2 * M.toReal * R ^ 2) := by
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le hr₀ hR
  have hcell : ∀ v ∈ {v : V | Hits F (Metric.closedBall (0 : Plane) R) v},
      (F.cell v : Set Plane) ⊆ Metric.closedBall (0 : Plane) (R + R / 100) :=
    fun v hv => cell_subset_closedBall_of_hits_of_diam_le F hv (hD R hR v hv)
  have h1 := localMassENN_le_setLIntegral_rootedFiniteEnergyDensity F hF hcell
  have h2 := hM (R + R / 100) (by linarith)
  have hm : (0 : ℝ) ≤ M.toReal := ENNReal.toReal_nonneg
  have hq : (R + R / 100) ^ 2 ≤ 2 * R ^ 2 := by nlinarith
  have hstep : ENNReal.ofReal ((R + R / 100) ^ 2) * ENNReal.ofReal M.toReal
      ≤ ENNReal.ofReal (2 * M.toReal * R ^ 2) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (R + R / 100) ^ 2 * M.toReal ≤ (2 * R ^ 2) * M.toReal :=
          mul_le_mul_of_nonneg_right hq hm
      _ = 2 * M.toReal * R ^ 2 := by ring
  have h3 : ENNReal.ofReal ((R + R / 100) ^ 2) * M
      ≤ ENNReal.ofReal (2 * M.toReal * R ^ 2) := by
    refine le_trans (le_of_eq ?_) hstep
    rw [ENNReal.ofReal_toReal hMtop]
  exact le_trans h1 (le_trans h2 h3)

/-- **`hD` from the checked large-cell decay.**  The manuscript's local diameter hypothesis
is the `ε = 1/100` instance of `Spatial.maxDiamHittingBall_sublinear`: the starting radius is
random and finite, and every radius above it is preserved. -/
theorem exists_diameter_bound_of_maxDiamHittingBall_sublinear (F : IndexedCells V)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      Spatial.maxDiamHittingBall F R ≤ ENNReal.ofReal (ε * R)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ v : V,
      Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100 := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hsub (1 / 100) (by norm_num)
  refine ⟨R₀, hR₀pos, fun R hR v hv => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le hR₀pos hR
  have hmem : ENNReal.ofReal (Metric.diam (F.cell v : Set Plane))
      ≤ Spatial.maxDiamHittingBall F R :=
    le_iSup (fun w : {w : V // Hits F (Metric.closedBall (0 : Plane) R) w} =>
      ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane))) ⟨v, hv⟩
  have hle : ENNReal.ofReal (Metric.diam (F.cell v : Set Plane))
      ≤ ENNReal.ofReal (1 / 100 * R) := le_trans hmem (hR₀ R hR)
  have hfin := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
  linarith

/-- **The full hypothesis tuple of manuscript Proposition `r:prop:log`.**  From the
large-cell decay and a finite ball-maximal constant for the rooted (FE) density, one obtains
a finite starting radius `r₀` — at least the norm of the representative of the root — and a
finite constant `C`, valid simultaneously at every radius `R ≥ r₀`. -/
theorem exists_logCutoff_hypotheses
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane) (o : V)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      Spatial.maxDiamHittingBall F R ≤ ENNReal.ofReal (ε * R))
    {M : ℝ≥0∞} (hMtop : M ≠ ∞)
    (hM : ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity F x ∂volume) ≤ ENNReal.ofReal (r ^ 2) * M) :
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ‖z o‖ ≤ r₀ ∧
      (∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
        Metric.diam (F.cell v : Set Plane) ≤ R / 100) ∧
      (∀ R : ℝ, r₀ ≤ R →
        LogCutoff.localMassENN F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v}
          ≤ ENNReal.ofReal (C * R ^ 2)) := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := exists_diameter_bound_of_maxDiamHittingBall_sublinear F hsub
  refine ⟨max R₀ ‖z o‖, 2 * M.toReal, lt_of_lt_of_le hR₀pos (le_max_left _ _),
    by positivity, le_max_right _ _, ?_, ?_⟩
  · exact fun R hR v hv => hR₀ R (le_trans (le_max_left _ _) hR) v hv
  · exact localMassENN_hittingBall_le_of_ballBound F hF
      (lt_of_lt_of_le hR₀pos (le_max_left _ _))
      (fun R hR v hv => hR₀ R (le_trans (le_max_left _ _) hR) v hv) hMtop hM

end Deterministic

section Environment

/-- **The almost-sure environment form.**  Under mass transport and the manuscript's finite
(FE) moment, almost every environment satisfies the local diameter hypothesis for some finite
random radius; adding an almost-sure finite ball-maximal constant for the rooted (FE) density
gives the full hypothesis tuple of Proposition `r:prop:log`, for every choice of cell
representatives and of root. -/
theorem ae_exists_logCutoff_hypotheses (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (hMax : ∀ᵐ e ∂ν, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity (decode e) x ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M) :
    ∀ᵐ e ∂ν, ∀ (z : Vertex e.val → Plane) (o : Vertex e.val),
      ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ‖z o‖ ≤ r₀ ∧
        (∀ R : ℝ, r₀ ≤ R → ∀ v : Vertex e.val,
          Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
          Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100) ∧
        (∀ R : ℝ, r₀ ≤ R →
          LogCutoff.localMassENN (decode e)
              {v : Vertex e.val | Hits (decode e) (Metric.closedBall (0 : Plane) R) v}
            ≤ ENNReal.ofReal (C * R ^ 2)) := by
  filter_upwards [Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE, hMax]
    with e he hMe z o
  obtain ⟨M, hMtop, hM⟩ := hMe
  exact exists_logCutoff_hypotheses (decode e) (decode_geometry e) z o he.2.1 hMtop hM

/-- The almost-sure local diameter hypothesis alone: this clause needs **no** maximal
inequality and **no** further producer, only mass transport and the (FE) moment. -/
theorem ae_exists_diameter_bound (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ v : Vertex e.val,
      Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
      Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100 := by
  filter_upwards [Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE] with e he
  exact exists_diameter_bound_of_maxDiamHittingBall_sublinear (decode e) he.2.1

end Environment

section Process

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nontrivial V]

end Process

end ReflectedGMS.AlmostSureCutoffBounds
