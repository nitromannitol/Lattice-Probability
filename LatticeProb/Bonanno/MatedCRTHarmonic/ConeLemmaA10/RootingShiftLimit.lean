/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.RootingShiftLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CircleAvgAlgebra
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.DistNormalization

/-!
# Circle-average support of the rooted field

For a root inside the unit disk, the logarithmic shift has a convergent mollified circle average
equal to zero on the unit circle. Adding it to a normalized whole-plane GFF therefore preserves
the normalization, so DMS14's final recentering is almost surely the identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric Set
open scoped Topology

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

/-- The mollified unit-circle averages of the DMS14 logarithmic shift converge to zero when the
root is in the open unit disk. -/
theorem tendsto_mollAvg_logRootingShift {γ : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    Tendsto (fun n => mollAvg (logRootingShift γ z) n 0 1) atTop (𝓝 0) := by
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
  rw [havg] at ht
  simpa [logRootingShift, MatedCRTHarmonic.MoTPort.ofFunC] using ht

/-- Adding the exact rooting shift leaves the unit-circle average zero almost surely under a
normalized whole-plane GFF. -/
theorem ae_circleAvg_add_logRootingShift_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    ∀ᵐ ω ∂P, circleAvg (h ω + logRootingShift γ z) 1 0 = 0 := by
  have hroot := tendsto_mollAvg_logRootingShift (γ := γ) hz
  have hshift : circleAvg (logRootingShift γ z) 1 0 = 0 :=
    circleAvg_eq_of_tendsto hroot
  filter_upwards [ae_tendsto_mollAvg hh.1 0 one_pos, hh.2] with ω ⟨a, ha⟩ hnorm
  have ha0 : a = 0 := by
    rw [← circleAvg_eq_of_tendsto ha, hnorm]
  have hha : Tendsto (fun n => mollAvg (h ω) n 0 1) atTop
      (𝓝 (circleAvg (h ω) 1 0)) := by
    rw [hnorm]
    simpa [ha0] using ha
  rw [circleAvg_add_of_tendsto hha hroot, hnorm]
  simp

/-- On the normalized-GFF support, the final unit-circle recentering in DMS14 A.10 does not
change the field after rooting at a point in the unit disk. -/
theorem ae_normalizedRootingMap_eq_add_logRootingShift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (γ : ℝ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    ∀ᵐ ω ∂P,
      addConst (h ω + logRootingShift γ z)
        (-circleAvg (h ω + logRootingShift γ z) 1 0) =
          h ω + logRootingShift γ z := by
  filter_upwards [ae_circleAvg_add_logRootingShift_eq_zero hh γ hz] with ω hω
  rw [hω, neg_zero, GFFLaw.addConst_zero']

end MatedCRTHarmonic.ConeLemmaA10

