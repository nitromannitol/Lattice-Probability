/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.DistNormalization at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.LogShift
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3

/-!
# Distributional normalization of the DMS14 logarithmic rooting shift

The representative of `logRootingShift` is singular at the root, but is continuous on a
neighbourhood of the unit circle when the root lies in the open unit disk. We reuse the
localized circle-average bridge `ConeArea3.tendsto_mollAvg_ofFunC` to identify its
distributional circle average with the classical one computed in `LogShift`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Metric Set

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric

lemma continuousOn_logRootingShiftFun_compl_singleton (γ : ℝ) (z : ℂ) :
    ContinuousOn (logRootingShiftFun γ z) ({z}ᶜ : Set ℂ) := by
  intro w hw
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr (by simpa using hw)
  have hlog : ContinuousAt (fun u : ℂ => Real.log ‖u - z‖) w :=
    ((continuousAt_id.sub continuousAt_const).norm.log (norm_ne_zero_iff.mpr hwz))
  change ContinuousWithinAt (fun u : ℂ =>
    -γ * Real.log ‖u - z‖ + γ * Real.log (max ‖u‖ (1 : ℝ))) ({z}ᶜ : Set ℂ) w
  exact ((continuousAt_const.neg.mul hlog).add
    (continuousAt_const.mul continuous_log_max_norm_one.continuousAt)).continuousWithinAt

lemma measurable_logRootingShiftFun (γ : ℝ) (z : ℂ) :
    Measurable (logRootingShiftFun γ z) := by
  exact (measurable_const.neg.mul
    ((continuous_id.sub continuous_const).norm.measurable.log)).add
      (measurable_const.mul continuous_log_max_norm_one.measurable)

/-- For a root in the open unit disk, the distribution defined by the exact DMS14 logarithmic
shift has zero circle average on the unit circle. -/
theorem circleAvg_logRootingShift_eq_zero {γ : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    circleAvg (logRootingShift γ z) 1 0 = 0 := by
  have hz' : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
  have hsphere : sphere (0 : ℂ) 1 ⊆ ({z}ᶜ : Set ℂ) := by
    intro w hw
    have hw_norm : ‖w‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hw
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hwz
    rw [hwz] at hw_norm
    linarith
  have ht := MatedCRTHarmonic.MoTPort.ConeArea3.tendsto_mollAvg_ofFunC
    (locallyIntegrable_logRootingShiftFun γ z) isOpen_compl_singleton
    (continuousOn_logRootingShiftFun_compl_singleton γ z) one_pos hsphere
  have havg : Real.circleAverage (logRootingShiftFun γ z) 0 1 = 0 := by
    rw [← QuantumZipper.CoordReg.integral_circleUnif_eq_circleAverage
      (measurable_logRootingShiftFun γ z)]
    exact integral_logRootingShiftFun_circle_eq_zero hz
  apply CircleAvg.circleAvg_eq_of_tendsto
  rw [havg] at ht
  simpa [logRootingShift, MatedCRTHarmonic.MoTPort.ofFunC] using ht

/-- Resetting the unit-circle average of the exact DMS14 shift leaves its distribution
unchanged. -/
theorem normalize_logRootingShift_eq_self {γ : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    addConst (logRootingShift γ z) (-circleAvg (logRootingShift γ z) 1 0) =
      logRootingShift γ z := by
  rw [circleAvg_logRootingShift_eq_zero hz, neg_zero, GFFLaw.addConst_zero']

end MatedCRTHarmonic.ConeLemmaA10

