/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.Rotation at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFFWP
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# Whole-plane GFF rotation invariance for IGC

The field-level rotation operation is reused from the ported imaginary-geometry field layer.
This file proves its invariance directly at LQGMetric's whole-plane GFF definition.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Distributions

namespace MatedCRTHarmonic.IGLaw

open LQGMetric
open MatedCRTHarmonic.MoTPort

/-- Pull a mean-zero test function back by the field rotation used by `rotateField`. -/
def rotationPullback (θ : ℝ) (φ : TestC0) : TestC0 :=
  ⟨FieldOps.testPullCLE (rotation (Circle.exp (-θ))).toContinuousLinearEquiv φ.1, by
    change ∫ x, φ.1 (rotation (Circle.exp (-θ)) x) = 0
    have hmp := (rotation (Circle.exp (-θ))).measurePreserving
    have h := hmp.integral_comp
      (rotation (Circle.exp (-θ))).toHomeomorph.measurableEmbedding (fun x : ℂ => φ.1 x)
    rw [h, φ.2]
  ⟩

/-- `logCov` is invariant under simultaneous rotation of both test functions. -/
theorem logCov_rotationPullback (θ : ℝ) (φ ψ : TestC0) :
    logCov (rotationPullback θ φ).1 (rotationPullback θ ψ).1 = logCov φ.1 ψ.1 := by
  let R := rotation (Circle.exp (-θ))
  have hmp : MeasurePreserving R (volume : Measure ℂ) volume := R.measurePreserving
  have hme : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  have hdist (x y : ℂ) : ‖R x - R y‖ = ‖x - y‖ := by
    rw [← R.map_sub, R.norm_map]
  have hinner (x : ℂ) :
      (∫ y, φ.1 (R x) * (-Real.log ‖R x - R y‖) * ψ.1 (R y)) =
        ∫ y, φ.1 (R x) * (-Real.log ‖R x - y‖) * ψ.1 y := by
    have h := hmp.integral_comp hme
      (fun y : ℂ => φ.1 (R x) * (-Real.log ‖R x - y‖) * ψ.1 y)
    convert h using 1
  have houter :
      (∫ x, ∫ y, φ.1 (R x) * (-Real.log ‖R x - y‖) * ψ.1 y) =
        ∫ x, ∫ y, φ.1 x * (-Real.log ‖x - y‖) * ψ.1 y := by
    have h := hmp.integral_comp hme
      (fun x : ℂ => ∫ y, φ.1 x * (-Real.log ‖x - y‖) * ψ.1 y)
    convert h using 1
  unfold logCov
  calc
    (∫ x, ∫ y, (rotationPullback θ φ).1 x * (-Real.log ‖x - y‖) *
        (rotationPullback θ ψ).1 y) =
      ∫ x, ∫ y, φ.1 (R x) * (-Real.log ‖R x - R y‖) * ψ.1 (R y) := by
        apply integral_congr_ae
        filter_upwards [] with x
        apply integral_congr_ae
        filter_upwards [] with y
        change φ.1 (R x) * (-Real.log ‖x - y‖) * ψ.1 (R y) = _
        rw [← hdist]
    _ = ∫ x, ∫ y, φ.1 (R x) * (-Real.log ‖R x - y‖) * ψ.1 y := by
        apply integral_congr_ae
        exact ae_of_all _ hinner
    _ = ∫ x, ∫ y, φ.1 x * (-Real.log ‖x - y‖) * ψ.1 y := houter

/-- Rotating a whole-plane GFF gives a whole-plane GFF, with its additive constant left
unconstrained as in LQGMetric's normalization. -/
theorem IsWholePlaneGFF.rotateField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (θ : ℝ) :
    IsWholePlaneGFF (fun ω => MatedCRTHarmonic.MoTPort.rotateField θ (h ω)) P := by
  refine ⟨(MatedCRTHarmonic.MoTPort.measurable_rotateField θ).comp hh.measurable,
    ?_, ?_, ?_⟩
  · have hg := hh.gaussian.comp_right (rotationPullback θ)
    refine hg.congr fun φ => Eventually.of_forall fun ω => ?_
    rfl
  · intro φ
    exact hh.centered (rotationPullback θ φ)
  · intro φ ψ
    rw [show (fun ω => MatedCRTHarmonic.MoTPort.rotateField θ (h ω) φ.1) =
        (fun ω => h ω (rotationPullback θ φ).1) from rfl,
      show (fun ω => MatedCRTHarmonic.MoTPort.rotateField θ (h ω) ψ.1) =
        (fun ω => h ω (rotationPullback θ ψ).1) from rfl,
      hh.covariance_eq]
    exact logCov_rotationPullback θ φ ψ

/-- The law of the mean-zero pairing process is rotation invariant. This is equality of the
whole-plane GFF modulo additive constants, rather than a claim about an unnormalized field law. -/
theorem map_pairProc_rotateField_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (θ : ℝ) :
    P.map (GFFLaw.pairProc (fun ω => MatedCRTHarmonic.MoTPort.rotateField θ (h ω))) =
      P.map (GFFLaw.pairProc h) :=
  GFFLaw.map_pairProc_eq (MatedCRTHarmonic.IGLaw.IsWholePlaneGFF.rotateField hh θ) hh

end MatedCRTHarmonic.IGLaw
