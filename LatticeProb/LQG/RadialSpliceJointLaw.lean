import LatticeProb.LQG.RadialSpliceGaussian
import LatticeProb.LQG.RadialSpliceLateralIndep

/-! # Joint law of a radial splice and the lateral field -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- An independent Brownian splice and the original centered radial version
have the same joint law with the lateral part of a whole-plane GFF. -/
theorem IsWholePlaneGFF.map_lateralPart_twoSided_eq_radialVersion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hW : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P) :
    P.map (fun ω => (lateralPartC (X ω), twoSided (W ω)
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)) =
      P.map (fun ω => (lateralPartC (X ω), R (X ω))) := by
  have := hX.gaussian.isProbabilityMeasure
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  have hVm : Measurable V := ContinuousMap.measurable_iff_eval.2 fun t =>
    (ContinuousMap.measurable_eval (-(t : ℝ))).comp (hRm.comp hX.measurable)
  have hSm : Measurable (fun ω => twoSided (W ω) (V ω)) :=
    measurable_twoSided.comp (hWm.prodMk hVm)
  have hLm : Measurable (fun ω => lateralPartC (X ω)) :=
    MatedCRTHarmonic.ConeScaling.measurable_lateralPart.comp hX.measurable
  have hRpath : Measurable (fun ω => R (X ω)) := hRm.comp hX.measurable
  have hLS := IsWholePlaneGFF.indepFun_lateralPart_twoSided hX hRm hR hWm hXW
  have hLR := (IsWholePlaneGFF.indepFun_lateralPart_radialPath_prodMk
    hX hRm hR hWm hXW).comp measurable_id measurable_fst
  change P.map (fun ω => (lateralPartC (X ω), twoSided (W ω) (V ω))) =
    P.map (fun ω => (lateralPartC (X ω), R (X ω)))
  rw [(indepFun_iff_map_prod_eq_prod_map_map hLm.aemeasurable hSm.aemeasurable).1 hLS,
    (indepFun_iff_map_prod_eq_prod_map_map hLm.aemeasurable hRpath.aemeasurable).1 hLR,
    IsWholePlaneGFF.map_twoSided_exterior_eq_radialVersion hX hRm hR hWm hW hXW]

end LatticeProb.LQG
