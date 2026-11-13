/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.AreaClockLocalFiniteness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.LocalAreaSummability
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceHoldingDivergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnClockCompatibility
import LatticeProb.Bonanno.ReflectedGMS.Forms.JumpOccupationIntegrability
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1StateTimeIntegrability
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ReturnCycleSpatialBoundedness

/-!
# Local finiteness of the actual area clock

The clock is the existing `PositiveOccupationClock.weightedOccupationClock`
with density `cellArea / m`.  We first localize to cells meeting a fixed
closed ball.  Stationarity of the summable fast speed measure gives its exact
finite mean under the speed mixture, hence a finite-mean bound under every
fixed starting law.  A compact-time bound on the visited spatial
representatives then removes the localization pathwise.
-/

-- Merged from `ReflectedGMS/Forms/PositiveOccupationClock.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_PositiveOccupationClock

/- The occupation integral of a nonnegative vertex density has infinite range
as soon as the density is positive at the starting vertex. -/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ReflectedGMS.PositiveOccupationClock

open ReflectedWalk ReflectedWalk.Theorem16
open TargetOccupationClock

universe u

variable {V : Type u} {Ω : Type u} [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable V]

/- The elapsed-time integral of a nonnegative density along a path. -/
noncomputable def weightedOccupationClock (q : V → ℝ≥0∞)
    (X : ℝ≥0 → Ω → Option V) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Icc (0 : ℝ) (t : ℝ), (X (Real.toNNReal s) ω).elim 0 q

/- Occupation of one vertex, multiplied by its density, is a lower bound for
the weighted clock.  Measurability is required only to identify the occupation
set measure with its indicator integral. -/

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V} [Nontrivial V]

/- Under the actual reflected-walk law, the weighted occupation clock is
unbounded over finite horizons if the density is positive at the start. -/

end ReflectedGMS.PositiveOccupationClock

end Merged_PositiveOccupationClock

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.AreaClockLocalFiniteness

open ReflectedWalk ReflectedWalk.Theorem16
open PositiveOccupationClock

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The manuscript area-clock density `a_v / m(v)`, in the codomain of the
actual weighted occupation clock. -/
noncomputable def areaClockDensity (F : IndexedCells V) (m : V → ℝ) (v : V) : ℝ≥0∞ :=
  ENNReal.ofReal (StatementIngredients.cellArea F v / m v)

/-- The actual area clock, using the repository's weighted occupation clock. -/
noncomputable def areaClock (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (t : ℝ≥0) (ω : PF.Ω) : ℝ≥0∞ :=
  weightedOccupationClock (areaClockDensity F m) PF.X t ω

/-- Area-clock density restricted to cells meeting a fixed closed ball. -/
noncomputable def localAreaClockDensity (F : IndexedCells V) (m : V → ℝ)
    (R : ℝ) (v : V) : ℝ≥0∞ := by
  classical
  exact if Hits F (Metric.closedBall (0 : Plane) R) v then areaClockDensity F m v else 0

/-- The fixed-ball localization of the actual area clock. -/
noncomputable def localAreaClock (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (R : ℝ) (t : ℝ≥0) (ω : PF.Ω) : ℝ≥0∞ :=
  weightedOccupationClock (localAreaClockDensity F m R) PF.X t ω

/-- A jointly measurable dyadic version of a weighted occupation clock. -/
noncomputable def dyadicWeightedOccupationClock (PF : ProcessFamily V)
    (q : V → ℝ≥0∞) (t : ℝ≥0) (ω : PF.Ω) : ℝ≥0∞ :=
  ∫⁻ r in Icc (0 : ℝ) (t : ℝ),
    (dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 q

theorem measurable_dyadicWeightedOccupationClock (PF : ProcessFamily V)
    (q : V → ℝ≥0∞) (t : ℝ≥0) :
    Measurable (dyadicWeightedOccupationClock PF q t) := by
  let H : PF.Ω → ℝ → ℝ≥0∞ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator
      (fun r ↦ (dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 q) r
  have hH : Measurable (Function.uncurry H) := by
    dsimp only [H]
    exact ((measurable_of_countable (fun p : Option V ↦ p.elim 0 q)).comp
      (measurable_swap_toNNReal
        (measurable_uncurry_dyadicLimit PF.measurable_X))).indicator
          (measurable_snd measurableSet_Icc)
  change Measurable fun ω => ∫⁻ r in Icc (0 : ℝ) (t : ℝ),
    (dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 q
  simpa only [H, Function.uncurry_apply_pair,
    lintegral_indicator measurableSet_Icc] using
      hH.lintegral_prod_right' (ν := (volume : Measure ℝ))

/-- On the actual right-regular reflected path, the measurable dyadic clock
and the literal weighted occupation clock agree at every horizon. -/
theorem ae_dyadicWeightedOccupationClock_eq_weightedOccupationClock
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (q : V → ℝ≥0∞) (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      dyadicWeightedOccupationClock PF q t ω =
        weightedOccupationClock q PF.X t ω := by
  filter_upwards [ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1] with ω hω
  intro t
  apply lintegral_congr
  intro r
  rw [hω (Real.toNNReal r)]

/-- The local density has exactly the locally summed cell area as its mass
against the fast speed measure. -/
theorem lintegral_localAreaClockDensity_vertexSpeedMeasure
    (F : IndexedCells V) (hF : Geometry F) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (R : ℝ) :
    (∫⁻ v, localAreaClockDensity F m R v ∂vertexSpeedMeasure m) =
      ∑' v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v},
        ENNReal.ofReal (StatementIngredients.cellArea F v.1) := by
  classical
  rw [lintegral_countable']
  simp only [vertexSpeedMeasure_singleton]
  calc
    (∑' v : V, localAreaClockDensity F m R v * ENNReal.ofReal (m v)) =
        ∑' v : V, if hv : Hits F (Metric.closedBall (0 : Plane) R) v then
          ENNReal.ofReal (StatementIngredients.cellArea F v) else 0 := by
      apply tsum_congr
      intro v
      by_cases hv : Hits F (Metric.closedBall (0 : Plane) R) v
      · simp only [localAreaClockDensity, hv, if_pos, areaClockDensity]
        rw [← ENNReal.ofReal_mul (div_nonneg
          (StatementIngredients.cellArea_pos F hF v).le (hm v).le)]
        congr 1
        field_simp [(hm v).ne']
      · simp [localAreaClockDensity, hv]
    _ = ∑' v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v},
          ENNReal.ofReal (StatementIngredients.cellArea F v.1) := by
      exact (tsum_subtype {v : V | Hits F (Metric.closedBall (0 : Plane) R) v}
        (fun v ↦ ENNReal.ofReal (StatementIngredients.cellArea F v))).symm

/-- At each real time, the dyadic state has exactly the stationary speed
mixture as its law, so every nonnegative vertex density has its speed mass. -/
theorem lintegral_dyadicWeightedOccupationDensity_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : V → ℝ≥0∞) (r : ℝ) :
    (∫⁻ ω, (dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 q
      ∂reflectedSpeedLaw PF m) =
      ∫⁻ v, q v ∂vertexSpeedMeasure m := by
  calc
    (∫⁻ ω, (dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 q
        ∂reflectedSpeedLaw PF m) =
        ∫⁻ p, p.elim 0 q
          ∂(reflectedSpeedLaw PF m).map
            (dyadicLimit PF.X (Real.toNNReal r)) :=
      (lintegral_map (μ := reflectedSpeedLaw PF m)
        (f := fun p : Option V ↦ p.elim 0 q)
        (g := dyadicLimit PF.X (Real.toNNReal r))
        (measurable_of_countable _)
        (measurable_dyadicLimit PF.measurable_X _)).symm
    _ = ∫⁻ p, p.elim 0 q
          ∂(vertexSpeedMeasure m).map (some : V → Option V) := by
      rw [reflectedSpeedLaw_map_dyadicState h hG hm hmsum r]
    _ = ∫⁻ v, q v ∂vertexSpeedMeasure m := by
      rw [lintegral_map (measurable_of_countable _)
        (measurable_of_countable (some : V → Option V))]
      rfl

/-- Exact finite-horizon mean of the dyadic weighted clock under the
unnormalized stationary speed mixture. -/
theorem lintegral_dyadicWeightedOccupationClock_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : V → ℝ≥0∞) (t : ℝ≥0) :
    (∫⁻ ω, dyadicWeightedOccupationClock PF q t ω
      ∂reflectedSpeedLaw PF m) =
      ENNReal.ofReal (t : ℝ) * (∫⁻ v, q v ∂vertexSpeedMeasure m) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let H : PF.Ω → ℝ → ℝ≥0∞ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator
      (fun r ↦ (dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 q) r
  have hH : Measurable (Function.uncurry H) := by
    dsimp only [H]
    exact ((measurable_of_countable (fun p : Option V ↦ p.elim 0 q)).comp
      (measurable_swap_toNNReal
        (measurable_uncurry_dyadicLimit PF.measurable_X))).indicator
          (measurable_snd measurableSet_Icc)
  calc
    (∫⁻ ω, dyadicWeightedOccupationClock PF q t ω
        ∂reflectedSpeedLaw PF m) =
        ∫⁻ ω, ∫⁻ r, H ω r ∂volume ∂reflectedSpeedLaw PF m := by
      apply lintegral_congr
      intro ω
      simp only [dyadicWeightedOccupationClock, H,
        lintegral_indicator measurableSet_Icc]
    _ = ∫⁻ r, ∫⁻ ω, H ω r ∂reflectedSpeedLaw PF m ∂volume := by
      rw [lintegral_lintegral_swap hH.aemeasurable]
    _ = ∫⁻ r : ℝ in Icc 0 (t : ℝ),
        (∫⁻ v, q v ∂vertexSpeedMeasure m) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro r
      by_cases hr : r ∈ Icc (0 : ℝ) (t : ℝ)
      · simp only [H, Set.indicator_of_mem hr]
        exact lintegral_dyadicWeightedOccupationDensity_reflectedSpeedLaw
          h hG hm hmsum q r
      · simp [H, Set.indicator_of_notMem hr]
    _ = ENNReal.ofReal (t : ℝ) *
        (∫⁻ v, q v ∂vertexSpeedMeasure m) := by
      rw [setLIntegral_const, Real.volume_Icc]
      simp only [sub_zero]
      rw [mul_comm]

/-- Fixed-start expected local area clock, in the detailed-balance form used
in manuscript theorem `p:thm:areaclock`. -/
theorem mul_lintegral_dyadicLocalAreaClock_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (F : IndexedCells V) (hF : Geometry F)
    (R : ℝ) (t : ℝ≥0) (z : V) :
    ENNReal.ofReal (m z) *
      (∫⁻ ω, dyadicWeightedOccupationClock PF
        (localAreaClockDensity F m R) t ω ∂PF.P z) ≤
      ENNReal.ofReal (t : ℝ) *
        ∑' v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v},
          ENNReal.ofReal (StatementIngredients.cellArea F v.1) := by
  have hb := lintegral_mono' (smul_start_le_reflectedSpeedLaw PF m z)
    (le_refl (dyadicWeightedOccupationClock PF
      (localAreaClockDensity F m R) t))
  rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_dyadicWeightedOccupationClock_reflectedSpeedLaw h hG hm hmsum,
    lintegral_localAreaClockDensity_vertexSpeedMeasure F hF m hm R] at hb
  exact hb

/-- Every fixed-ball localization of the literal area clock is finite almost
surely under each starting law. -/
theorem localAreaClock_lt_top_ae
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (F : IndexedCells V) (hF : Geometry F)
    (R : ℝ)
    (hsum : Summable
      (fun v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v} ↦
        StatementIngredients.cellArea F v.1))
    (t : ℝ≥0) (z : V) :
    ∀ᵐ ω ∂PF.P z, localAreaClock F m PF R t ω < ∞ := by
  have hbound := mul_lintegral_dyadicLocalAreaClock_le
    h hG hm hmsum F hF R t z
  have hrhs : ENNReal.ofReal (t : ℝ) *
      (∑' v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v},
        ENNReal.ofReal (StatementIngredients.cellArea F v.1)) < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum.tsum_ofReal_lt_top
  have hprod : ENNReal.ofReal (m z) *
      (∫⁻ ω, dyadicWeightedOccupationClock PF
        (localAreaClockDensity F m R) t ω ∂PF.P z) < ∞ :=
    hbound.trans_lt hrhs
  have hmean : (∫⁻ ω, dyadicWeightedOccupationClock PF
      (localAreaClockDensity F m R) t ω ∂PF.P z) < ∞ := by
    by_contra hn
    have htop : (∫⁻ ω, dyadicWeightedOccupationClock PF
        (localAreaClockDensity F m R) t ω ∂PF.P z) = ∞ :=
      top_le_iff.mp (not_lt.mp hn)
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (hm z)).ne'] at hprod
    exact (lt_irrefl _ hprod)
  filter_upwards [ae_lt_top
      (measurable_dyadicWeightedOccupationClock PF
        (localAreaClockDensity F m R) t) hmean.ne,
    ae_dyadicWeightedOccupationClock_eq_weightedOccupationClock h
      (localAreaClockDensity F m R) z] with ω hfinite heq
  change weightedOccupationClock (localAreaClockDensity F m R) PF.X t ω < ∞
  rw [← heq t]
  exact hfinite

/-- Increasing the finite horizon can only increase a localized clock. -/
theorem localAreaClock_mono_time (F : IndexedCells V) (m : V → ℝ)
    (PF : ProcessFamily V) (R : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (ω : PF.Ω) :
    localAreaClock F m PF R s ω ≤ localAreaClock F m PF R t ω := by
  unfold localAreaClock weightedOccupationClock
  apply lintegral_mono'
      (Measure.restrict_mono (Set.Icc_subset_Icc_right (by exact_mod_cast hst)) le_rfl)
  exact le_rfl

/-- Compact-time boundedness of actual cell representatives removes the
fixed-ball localization.  Countable integer radii and horizons make all local
finiteness events simultaneous before the random spatial bound is chosen. -/
theorem areaClock_finite_on_compact_times_of_spatialBounded
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (F : IndexedCells V) (hF : Geometry F)
    (zrep : V → Plane) (hzrep : StatementIngredients.CellRepresentatives F zrep)
    (hD : ∀ R : ℝ, 0 ≤ R → Spatial.maxDiamHittingBall F R < ∞)
    (o : V)
    (hbounded : ∀ᵐ ω ∂PF.P o, ∀ T : ℝ≥0, ∃ C : ℝ,
      ∀ t : ℝ≥0, t ≤ T → ∀ y : V, PF.X t ω = some y → ‖zrep y‖ ≤ C) :
    ∀ᵐ ω ∂PF.P o, ∀ T : ℝ≥0, areaClock F m PF T ω < ∞ := by
  have hlocal : ∀ᵐ ω ∂PF.P o, ∀ K N : ℕ,
      localAreaClock F m PF (K : ℝ) (N : ℝ≥0) ω < ∞ := by
    rw [ae_all_iff]
    intro K
    rw [ae_all_iff]
    intro N
    exact localAreaClock_lt_top_ae h hG hm hmsum F hF (K : ℝ)
      (summable_cellArea_hitting_closedBall_and_tsum_le F hF
        (Nat.cast_nonneg K) (hD K (Nat.cast_nonneg K))).1
      (N : ℝ≥0) o
  filter_upwards [hlocal, hbounded] with ω hlocalω hboundedω
  intro T
  obtain ⟨N, hTN⟩ := exists_nat_ge T
  obtain ⟨C, hC⟩ := hboundedω (N : ℝ≥0)
  obtain ⟨K, hCK⟩ := exists_nat_ge (max 0 C)
  have hTC : T ≤ (N : ℝ≥0) := hTN
  have heq : areaClock F m PF T ω = localAreaClock F m PF (K : ℝ) T ω := by
    unfold areaClock localAreaClock weightedOccupationClock
    apply setLIntegral_congr_fun measurableSet_Icc
    intro r hr
    have hrT : Real.toNNReal r ≤ T := by
      rw [← NNReal.coe_le_coe]
      simpa only [Real.coe_toNNReal r hr.1] using hr.2
    have hrN : Real.toNNReal r ≤ (N : ℝ≥0) := hrT.trans hTC
    cases hx : PF.X (Real.toNNReal r) ω with
    | none => simp [hx]
    | some y =>
        have hyC : ‖zrep y‖ ≤ C := hC (Real.toNNReal r) hrN y hx
        have hyK : ‖zrep y‖ ≤ (K : ℝ) :=
          hyC.trans ((le_max_right 0 C).trans hCK)
        have hhit : Hits F (Metric.closedBall (0 : Plane) (K : ℝ)) y :=
          ⟨zrep y, hzrep y, by
            simpa only [Metric.mem_closedBall, dist_zero_right] using hyK⟩
        simp [hx, localAreaClockDensity, hhit]
  calc
    areaClock F m PF T ω = localAreaClock F m PF (K : ℝ) T ω := heq
    _ ≤ localAreaClock F m PF (K : ℝ) (N : ℝ≥0) ω :=
      localAreaClock_mono_time F m PF (K : ℝ) hTC ω
    _ < ∞ := hlocalω K N

/-- First (local-finiteness) clause of manuscript theorem `p:thm:areaclock`.
The spatial cutoff criterion is applied to an actual point chosen in each cell,
so bounded representative radius places every visited cell in a fixed ball. -/
theorem areaClock_finite_on_compact_times
    (F : IndexedCells V) {m : V → ℝ} {hmin : F.graph.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk F.graph (fun v ↦ F.graph.pi v / m v) hmin PF)
    (hF : Geometry F) (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    (zrep : V → Plane) (hzrep : StatementIngredients.CellRepresentatives F zrep)
    (hD : ∀ R : ℝ, 0 ≤ R → Spatial.maxDiamHittingBall F R < ∞)
    (o : V)
    (hvan : ExcursionBoundedRange.VanishingFarEnergy F.graph o
      (fun v ↦ ‖zrep v‖)) :
    ∀ᵐ ω ∂PF.P o, ∀ T : ℝ≥0, areaClock F m PF T ω < ∞ := by
  have hG : F.graph.toSimpleGraph.Connected := hF.2.2.2.2.2.1
  have hw : ∀ v, 0 < F.graph.pi v / m v := fun v =>
    div_pos (F.graph.pi_pos_of_connected hG v) (hm v)
  exact areaClock_finite_on_compact_times_of_spatialBounded
    h hG hm hmsum F hF zrep hzrep hD o
      (ReturnCycleSpatialBoundedness.ae_forall_bddAbove_rho_on_boundedTime
        h hG hw hvan)

end ReflectedGMS.AreaClockLocalFiniteness
