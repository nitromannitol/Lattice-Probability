/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CylinderFieldExtensionality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CylinderMarginalUniqueness
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.CircleAvgFieldSupport

/-!
# Extensionality from bounded continuous field cylinders

This adapter composes the finite-cylinder uniqueness theorem with the circle-average support
argument to identify finite measures on `DistC` from their bounded continuous `ev0` cylinders.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.GFFInv

/-- Bounded continuous observables of all finite `ev0` cylinders determine a finite measure on
`DistC` when it is supported on the zero-circle-average fields where the mollified averages
converge. -/
theorem measure_eq_of_boundedContinuous_cylinder_integrals_of_circleAvgFieldSupport
    {μ ν : Measure DistC} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hobs : ∀ I : Finset TestC0, ∀ F : (I → ℝ) → ℝ,
      Continuous F → (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) →
        ∫ g, F (I.restrict (GFFLaw.ev0 g)) ∂μ =
          ∫ g, F (I.restrict (GFFLaw.ev0 g)) ∂ν)
    (hμ : ∀ᵐ g ∂μ, CircleAvgFieldSupport g)
    (hν : ∀ᵐ g ∂ν, CircleAvgFieldSupport g) : μ = ν := by
  have hX : AEMeasurable
      (fun g : DistC => fun ψ : TestC0 => g ψ.1) μ := by
    exact (measurable_pi_iff.2 fun (ψ : TestC0) => measurable_pair ψ.1).aemeasurable
  have hY : AEMeasurable
      (fun g : DistC => fun ψ : TestC0 => g ψ.1) ν := by
    exact (measurable_pi_iff.2 fun (ψ : TestC0) => measurable_pair ψ.1).aemeasurable
  have hpair : μ.map GFFLaw.ev0 = ν.map GFFLaw.ev0 := by
    change μ.map (fun g : DistC => fun ψ : TestC0 => g ψ.1) =
      ν.map (fun g : DistC => fun ψ : TestC0 => g ψ.1)
    exact map_process_eq_of_boundedContinuous_cylinder_integrals
        (X := fun (ψ : TestC0) (g : DistC) => g ψ.1)
        (Y := fun (ψ : TestC0) (g : DistC) => g ψ.1) hX hY hobs
  exact measure_eq_of_map_ev0_eq_of_circleAvg_zero
    (GFFLaw.integral_bumpTest 0 0) hpair
    (by simpa only [CircleAvgFieldSupport] using hμ)
    (by simpa only [CircleAvgFieldSupport] using hν)

end MatedCRTHarmonic.ConeLemmaA10

