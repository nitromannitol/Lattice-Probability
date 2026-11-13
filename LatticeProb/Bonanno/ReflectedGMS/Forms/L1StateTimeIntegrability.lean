/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.L1StateTimeIntegrability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.JumpOccupationIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-horizon integrability of speed-L¹ state observables

Stationarity and positive speed atoms give joint time/sample integrability
under every starting law. The canonical dyadic version supplies joint
measurability; its nonvertex value is zero.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS
open ReflectedWalk ReflectedWalk.Theorem16

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

noncomputable def dyadicStateObservable (PF : ProcessFamily V) (f : V → ℝ)
    (ω : PF.Ω) (r : ℝ) : ℝ :=
  (dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 f

theorem measurable_uncurry_dyadicStateObservable
    (PF : ProcessFamily V) (f : V → ℝ) :
    Measurable (Function.uncurry (dyadicStateObservable PF f)) :=
  (measurable_of_countable (fun q : Option V ↦ q.elim 0 f)).comp
    (measurable_swap_toNNReal
      (measurable_uncurry_dyadicLimit PF.measurable_X))

theorem reflectedSpeedLaw_map_dyadicState
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (r : ℝ) :
    (reflectedSpeedLaw PF m).map (dyadicLimit PF.X (Real.toNNReal r)) =
      (vertexSpeedMeasure m).map (some : V → Option V) := by
  rw [← reflectedSpeedLaw_map_position h hG hm hmsum (Real.toNNReal r)]
  apply Measure.map_congr
  change ∀ᵐ ω ∂reflectedSpeedLaw PF m,
    dyadicLimit PF.X (Real.toNNReal r) ω = PF.X (Real.toNNReal r) ω
  rw [ae_reflectedSpeedLaw_iff PF m hm]
  intro z
  filter_upwards [ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1] with ω hω
  exact hω (Real.toNNReal r)

theorem integrable_dyadicStateObservable_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {f : V → ℝ} (hf : Integrable f (vertexSpeedMeasure m))
    (r : ℝ) :
    Integrable (fun ω ↦ dyadicStateObservable PF f ω r) (reflectedSpeedLaw PF m) := by
  have hstate : Measurable (dyadicLimit PF.X (Real.toNNReal r)) :=
    measurable_dyadicLimit PF.measurable_X (Real.toNNReal r)
  have hraw : Measurable (fun q : Option V ↦ q.elim 0 f) := measurable_of_countable _
  apply (integrable_map_measure hraw.aestronglyMeasurable hstate.aemeasurable).mp
  rw [reflectedSpeedLaw_map_dyadicState h hG hm hmsum r]
  apply (integrable_map_measure hraw.aestronglyMeasurable
    (measurable_of_countable (some : V → Option V)).aemeasurable).mpr
  change Integrable f (vertexSpeedMeasure m)
  exact hf

theorem integral_norm_dyadicStateObservable_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (f : V → ℝ) (r : ℝ) :
    (∫ ω, ‖dyadicStateObservable PF f ω r‖ ∂reflectedSpeedLaw PF m) =
      ∫ x, ‖f x‖ ∂vertexSpeedMeasure m := by
  have hstate : Measurable (dyadicLimit PF.X (Real.toNNReal r)) :=
    measurable_dyadicLimit PF.measurable_X (Real.toNNReal r)
  have hraw : Measurable (fun q : Option V ↦ ‖q.elim 0 f‖) := measurable_of_countable _
  change (∫ ω, ‖(dyadicLimit PF.X (Real.toNNReal r) ω).elim 0 f‖
    ∂reflectedSpeedLaw PF m) = _
  rw [← integral_map hstate.aemeasurable hraw.aestronglyMeasurable,
    reflectedSpeedLaw_map_dyadicState h hG hm hmsum r,
    integral_map (measurable_of_countable (some : V → Option V)).aemeasurable
      hraw.aestronglyMeasurable]
  rfl

theorem integrable_dyadicStateObservable_time_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {f : V → ℝ} (hf : Integrable f (vertexSpeedMeasure m))
    (t : ℝ≥0) :
    Integrable (Function.uncurry (dyadicStateObservable PF f))
      ((reflectedSpeedLaw PF m).prod (volume.restrict (Icc 0 (t : ℝ)))) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  apply (integrable_prod_iff'
    (measurable_uncurry_dyadicStateObservable PF f).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun r ↦
    integrable_dyadicStateObservable_reflectedSpeedLaw h hG hm hmsum hf r), ?_⟩
  simp only [Function.uncurry_apply_pair,
    integral_norm_dyadicStateObservable_reflectedSpeedLaw h hG hm hmsum f]
  exact integrable_const _

/-- Every speed-L¹ state observable is jointly integrable over a finite time
interval under each actual starting law. -/
theorem integrable_dyadicStateObservable_time_start
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {f : V → ℝ} (hf : Integrable f (vertexSpeedMeasure m))
    (t : ℝ≥0) (z : V) :
    Integrable (Function.uncurry (dyadicStateObservable PF f))
      ((PF.P z).prod (volume.restrict (Icc 0 (t : ℝ)))) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have hi := (integrable_dyadicStateObservable_time_reflectedSpeedLaw
    h hG hm hmsum hf t).mono_measure
      (Measure.prod_mono (smul_start_le_reflectedSpeedLaw PF m z) le_rfl)
  rw [Measure.prod_smul_left] at hi
  exact (integrable_smul_measure (ENNReal.ofReal_pos.mpr (hm z)).ne'
    ENNReal.ofReal_ne_top).mp hi

end ReflectedGMS
