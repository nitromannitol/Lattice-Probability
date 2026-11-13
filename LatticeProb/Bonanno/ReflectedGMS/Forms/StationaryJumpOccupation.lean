/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryJumpOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryReflectedLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.ProcessOccupationLaplace
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedTrajectoryConditional
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Stationary occupation of the ordinary-edge jump rate

The dyadic path version makes the ordinary-edge carré-du-champ jointly
measurable.  Under the finite speed mixture, Tonelli and stationarity identify
its exact mean occupation.  Positivity of every speed atom then transfers
almost-sure finiteness to every starting law.

This is only an integrability statement for the candidate bracket density.  It
does not identify a stochastic bracket or remove boundary times pathwise.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The ordinary-edge carré-du-champ on the compact state type, with zero rate
at the collapsed end state. -/
noncomputable def stateVertexCarreDuChamp
    (G : ConductanceGraph V) (m : V → ℝ) (u : V → ℝ) : Option V → ℝ≥0∞
  | some x => ENNReal.ofReal (vertexCarreDuChamp G m u x)
  | none => 0

/-- The ordinary-edge carré-du-champ evaluated on the canonical jointly
measurable dyadic version of the raw reflected path. -/
noncomputable def dyadicVertexCarreDuChamp
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (ω : PF.Ω) (r : ℝ) : ℝ≥0∞ :=
  stateVertexCarreDuChamp G m u
    (dyadicLimit PF.X (Real.toNNReal r) ω)

/-- The dyadic ordinary-edge rate is jointly measurable in sample and real
time. -/
theorem measurable_uncurry_dyadicVertexCarreDuChamp
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) :
    Measurable (Function.uncurry
      (dyadicVertexCarreDuChamp PF G m u)) := by
  exact (measurable_of_countable (stateVertexCarreDuChamp G m u)).comp
    (measurable_swap_toNNReal
      (measurable_uncurry_dyadicLimit PF.measurable_X))

/-- Integrated dyadic ordinary-edge jump rate up to a deterministic time. -/
noncomputable def stationaryJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (t : ℝ≥0) (ω : PF.Ω) : ℝ≥0∞ :=
  ∫⁻ r : ℝ in Icc 0 (t : ℝ),
    dyadicVertexCarreDuChamp PF G m u ω r

theorem measurable_stationaryJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (t : ℝ≥0) :
    Measurable (stationaryJumpOccupation PF G m u t) := by
  let F : PF.Ω → ℝ → ℝ≥0∞ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator
      (dyadicVertexCarreDuChamp PF G m u ω) r
  have hF : Measurable (Function.uncurry F) := by
    dsimp only [F]
    exact (measurable_uncurry_dyadicVertexCarreDuChamp PF G m u).indicator
      (measurable_snd measurableSet_Icc)
  change Measurable (fun ω ↦ ∫⁻ r : ℝ in Icc 0 (t : ℝ),
    dyadicVertexCarreDuChamp PF G m u ω r)
  simpa only [F, lintegral_indicator measurableSet_Icc] using
    hF.lintegral_prod_right

/-- For positive speed atoms, an event has full speed-mixture measure exactly
when it has full measure under every starting law. -/
theorem ae_reflectedSpeedLaw_iff
    (PF : ProcessFamily V) (m : V → ℝ) (hm : ∀ z, 0 < m z)
    (p : PF.Ω → Prop) :
    (∀ᵐ ω ∂reflectedSpeedLaw PF m, p ω) ↔
      ∀ z, ∀ᵐ ω ∂PF.P z, p ω := by
  unfold reflectedSpeedLaw reflectedStartKernel
  rw [Measure.comp_eq_sum_of_countable, Measure.ae_sum_iff]
  simp_rw [vertexSpeedMeasure_singleton,
    Measure.ae_ennreal_smul_measure_iff
      (ENNReal.ofReal_pos.mpr (hm _)).ne']
  rfl

theorem lintegral_dyadicVertexCarreDuChamp_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (r : ℝ) :
    (∫⁻ ω, dyadicVertexCarreDuChamp PF G m u ω r
      ∂reflectedSpeedLaw PF m) = ENNReal.ofReal (2 * G.Energy u) := by
  have hver : ∀ᵐ ω ∂reflectedSpeedLaw PF m,
      dyadicLimit PF.X (Real.toNNReal r) ω = PF.X (Real.toNNReal r) ω := by
    rw [ae_reflectedSpeedLaw_iff PF m hm]
    intro z
    filter_upwards [ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1] with ω hω
    exact hω (Real.toNNReal r)
  calc
    (∫⁻ ω, dyadicVertexCarreDuChamp PF G m u ω r
        ∂reflectedSpeedLaw PF m) =
        ∫⁻ ω, stateVertexCarreDuChamp G m u
          (PF.X (Real.toNNReal r) ω) ∂reflectedSpeedLaw PF m := by
      apply lintegral_congr_ae
      filter_upwards [hver] with ω hω
      simp only [dyadicVertexCarreDuChamp, hω]
    _ = ∫⁻ q, stateVertexCarreDuChamp G m u q
          ∂(reflectedSpeedLaw PF m).map (PF.X (Real.toNNReal r)) :=
      (lintegral_map (measurable_of_countable _) (PF.measurable_X _)).symm
    _ = ∫⁻ q, stateVertexCarreDuChamp G m u q
          ∂(vertexSpeedMeasure m).map (some : V → Option V) := by
      rw [reflectedSpeedLaw_map_position h hG hm hmsum]
    _ = ∫⁻ x, ENNReal.ofReal (vertexCarreDuChamp G m u x)
          ∂vertexSpeedMeasure m := by
      rw [lintegral_map (measurable_of_countable _)
        (measurable_of_countable (some : V → Option V))]
      simp only [stateVertexCarreDuChamp]
    _ = ENNReal.ofReal (2 * G.Energy u) :=
      lintegral_vertexCarreDuChamp_vertexSpeedMeasure G m hm hu

/-- The exact expected integrated ordinary-edge jump rate under the finite
speed mixture. -/
theorem lintegral_stationaryJumpOccupation_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) :
    (∫⁻ ω, stationaryJumpOccupation PF G m u t ω
      ∂reflectedSpeedLaw PF m) =
      ENNReal.ofReal ((t : ℝ) * (2 * G.Energy u)) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let F : PF.Ω → ℝ → ℝ≥0∞ := fun ω r ↦
    (Icc (0 : ℝ) (t : ℝ)).indicator
      (dyadicVertexCarreDuChamp PF G m u ω) r
  have hF : Measurable (Function.uncurry F) := by
    dsimp only [F]
    exact (measurable_uncurry_dyadicVertexCarreDuChamp PF G m u).indicator
      (measurable_snd measurableSet_Icc)
  calc
    (∫⁻ ω, stationaryJumpOccupation PF G m u t ω
        ∂reflectedSpeedLaw PF m) =
        ∫⁻ ω, ∫⁻ r, F ω r ∂volume ∂reflectedSpeedLaw PF m := by
      apply lintegral_congr
      intro ω
      simp only [stationaryJumpOccupation, F,
        lintegral_indicator measurableSet_Icc]
    _ = ∫⁻ r, ∫⁻ ω, F ω r ∂reflectedSpeedLaw PF m ∂volume := by
      rw [lintegral_lintegral_swap hF.aemeasurable]
    _ = ∫⁻ r : ℝ in Icc 0 (t : ℝ),
        ENNReal.ofReal (2 * G.Energy u) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro r
      by_cases hr : r ∈ Icc (0 : ℝ) (t : ℝ)
      · simp only [F, Set.indicator_of_mem hr]
        exact lintegral_dyadicVertexCarreDuChamp_reflectedSpeedLaw
          h hG hm hmsum hu r
      · simp [F, Set.indicator_of_notMem hr]
    _ = ENNReal.ofReal ((t : ℝ) * (2 * G.Energy u)) := by
      rw [setLIntegral_const, Real.volume_Icc]
      simp only [sub_zero]
      rw [← ENNReal.ofReal_mul
        (mul_nonneg (by norm_num) (G.Energy_nonneg u))]
      ring

/-- Under every starting law, the integrated ordinary-edge rate is finite
almost surely at every fixed finite horizon. -/
theorem stationaryJumpOccupation_lt_top_ae
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) (z : V) :
    ∀ᵐ ω ∂PF.P z, stationaryJumpOccupation PF G m u t ω < ∞ := by
  have hfinite : ∀ᵐ ω ∂reflectedSpeedLaw PF m,
      stationaryJumpOccupation PF G m u t ω < ∞ := by
    apply ae_lt_top
      (measurable_stationaryJumpOccupation PF G m u t)
    rw [lintegral_stationaryJumpOccupation_reflectedSpeedLaw
      h hG hm hmsum hu t]
    exact ENNReal.ofReal_ne_top
  exact (ae_reflectedSpeedLaw_iff PF m hm _).mp hfinite z

end ReflectedGMS
