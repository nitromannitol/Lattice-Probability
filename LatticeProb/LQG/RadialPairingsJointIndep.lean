import LatticeProb.LQG.RadialPairingsLateralIndep
import LatticeProb.LQG.RadialUniform

/-! # Joint independence of radial pairings -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory LQGMetric
open MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- Radial pairings of a field-measurable centered radial version are independent
of the lateral field jointly with any random element independent of the field. -/
theorem IsWholePlaneGFF.indepFun_radialPairings_lateralPart_prodMk
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {ι : Type*} (ψ : ι → TestC0) {δ : Type*} [MeasurableSpace δ]
    {Z : Ω → δ} (hZ : Measurable Z) (hXZ : IndepFun X Z P) :
    IndepFun (fun ω i => pairW (symmTest (ψ i).1) (R (X ω)))
      (fun ω => (lateralPartC (X ω), Z ω)) P := by
  have := hX.gaussian.isProbabilityMeasure
  have hp : Measurable (fun h i => pairW (symmTest (ψ i).1) (R h)) :=
    measurable_pi_iff.2 fun i => (measurable_pairW _).comp hRm
  have hl := MatedCRTHarmonic.ConeScaling.measurable_lateralPart
  refine indepFun_prodMk_right_of_indepFun_prodMk (hp.comp hX.measurable)
    (hl.comp hX.measurable) hZ
    (IsWholePlaneGFF.indepFun_radialPairings_lateralPart hX (hRm.comp hX.measurable) hR ψ) ?_
  exact hXZ.comp (hp.prodMk hl) measurable_id

end LatticeProb.LQG
