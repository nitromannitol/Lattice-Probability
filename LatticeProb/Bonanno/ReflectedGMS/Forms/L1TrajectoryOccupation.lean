/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.L1TrajectoryOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1StateTimeIntegrability
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinMartingale

/-!
# Integrable trajectory occupation tests

Speed-L¹ state observables yield integrable finite-horizon trajectory tests,
including after deterministic time shifts. These discharge the integrability
premises of the unbounded future-trajectory Markov formula.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS
open ReflectedWalk ReflectedWalk.Theorem16

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

theorem integrable_trajectoryStateIntegral_law_of_L1
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {f : V → ℝ} (hf : Integrable f (vertexSpeedMeasure m))
    (t : ℝ≥0) (z : V) :
    Integrable (trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 f) t)
      (PF.law z) := by
  rw [ProcessFamily.law]
  apply (integrable_map_measure
    (measurable_trajectoryStateIntegral _ t).aestronglyMeasurable
    (measurable_pi_iff.mpr PF.measurable_X).aemeasurable).mpr
  exact (integrable_dyadicStateObservable_time_start h hG hm hmsum hf t z).integral_prod_left

/-- A shifted L¹ trajectory occupation is the difference of two ordinary
dyadic occupations, almost surely under every starting law. -/
theorem trajectoryStateIntegral_shifted_ae_eq_sub_of_L1
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {f : V → ℝ} (hf : Integrable f (vertexSpeedMeasure m))
    (s t : ℝ≥0) (z : V) :
    (fun ω ↦ trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 f) t
      (shiftedPath PF.X s ω)) =ᵐ[PF.P z]
    fun ω ↦ (∫ r : ℝ in Icc 0 ((s + t : ℝ≥0) : ℝ),
        dyadicStateObservable PF f ω r) -
      ∫ r : ℝ in Icc 0 (s : ℝ), dyadicStateObservable PF f ω r := by
  have hst := (integrable_dyadicStateObservable_time_start
    h hG hm hmsum hf (s + t) z).prod_right_ae
  have hs := (integrable_dyadicStateObservable_time_start
    h hG hm hmsum hf s z).prod_right_ae
  filter_upwards [hst, hs,
    ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hstω hsω hreg
  let g : ℝ → ℝ := dyadicStateObservable PF f ω
  have hist : IntervalIntegrable g volume 0 ((s + t : ℝ≥0) : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (s + t).coe_nonneg).mpr hstω
  have his : IntervalIntegrable g volume 0 (s : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le s.coe_nonneg).mpr hsω
  rw [trajectoryStateIntegral_shiftedPath_eq PF _ s t ω hreg]
  calc
    (∫ r : ℝ in Icc 0 (t : ℝ), (PF.X (Real.toNNReal r + s) ω).elim 0 f) =
        ∫ r : ℝ in (0 : ℝ)..(t : ℝ), g (r + (s : ℝ)) := by
      rw [intervalIntegral.integral_of_le t.coe_nonneg,
        integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      have hr0 : 0 ≤ r := hr.1.le
      have htime : Real.toNNReal (r + (s : ℝ)) = Real.toNNReal r + s := by
        apply NNReal.eq
        simp only [NNReal.coe_add, Real.coe_toNNReal _ hr0,
          Real.coe_toNNReal _ (add_nonneg hr0 s.coe_nonneg)]
      dsimp only [g, dyadicStateObservable]
      rw [dyadicLimit_eq_of_rightRegular hreg, htime]
    _ = ∫ r : ℝ in (s : ℝ)..((s + t : ℝ≥0) : ℝ), g r := by
      rw [intervalIntegral.integral_comp_add_right]
      simp only [zero_add, add_zero, NNReal.coe_add, add_comm]
    _ = (∫ r : ℝ in Icc 0 ((s + t : ℝ≥0) : ℝ), g r) -
        ∫ r : ℝ in Icc 0 (s : ℝ), g r := by
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (s + t).coe_nonneg,
        ← intervalIntegral.integral_of_le s.coe_nonneg]
      exact (intervalIntegral.integral_interval_sub_left hist his).symm

theorem integrable_trajectoryStateIntegral_shifted_of_L1
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {f : V → ℝ} (hf : Integrable f (vertexSpeedMeasure m))
    (s t : ℝ≥0) (z : V) :
    Integrable (fun ω ↦ trajectoryStateIntegral (fun q : Option V ↦ q.elim 0 f) t
      (shiftedPath PF.X s ω)) (PF.P z) := by
  have hst := (integrable_dyadicStateObservable_time_start
    h hG hm hmsum hf (s + t) z).integral_prod_left
  have hs := (integrable_dyadicStateObservable_time_start
    h hG hm hmsum hf s z).integral_prod_left
  exact (hst.sub hs).congr
    (trajectoryStateIntegral_shifted_ae_eq_sub_of_L1 h hG hm hmsum hf s t z).symm

end ReflectedGMS
