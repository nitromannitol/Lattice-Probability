import LatticeProb.LQG.RadialSpliceFieldLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P0

/-! # Normalized whole-plane GFF from a radial splice -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- Replacing the inner radial path with an independent Brownian path gives a
normalized whole-plane Gaussian free field. -/
theorem IsWholePlaneGFF.normalized_replField_twoSided
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hW : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P) :
    IsNormalizedWPGFF (replField X (fun ω => twoSided (W ω)
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)) P := by
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  have hVm : Measurable V := ContinuousMap.measurable_iff_eval.2 fun t =>
    (ContinuousMap.measurable_eval (-(t : ℝ))).comp (hRm.comp hX.measurable)
  have hSm : Measurable (fun ω => twoSided (W ω) (V ω)) :=
    measurable_twoSided.comp (hWm.prodMk hVm)
  have hNm := IsWholePlaneGFF.normalized_replField_radialVersion hX hRm hR
  exact LQGMetric.DFGPS.T12.isNormalizedWPGFF_of_map_eq
    (measurable_replField hX.measurable hSm) hNm
    (IsWholePlaneGFF.map_replField_twoSided_eq_normalized hX hNm hRm hR hWm hW hXW)

end LatticeProb.LQG
