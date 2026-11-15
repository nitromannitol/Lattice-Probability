import LatticeProb.LQG.RadialPathJointIndep

/-! # Independence of a radial splice and the lateral field -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- The lateral part is independent of the radial path jointly with any
measurable random element independent of the whole field. -/
theorem IsWholePlaneGFF.indepFun_lateralPart_radialPath_prodMk
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {δ : Type*} [MeasurableSpace δ] {Z : Ω → δ} (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) :
    IndepFun (fun ω => lateralPartC (X ω)) (fun ω => (R (X ω), Z ω)) P := by
  have := hX.gaussian.isProbabilityMeasure
  have hL := MatedCRTHarmonic.ConeScaling.measurable_lateralPart
  have hRA := IsWholePlaneGFF.indepFun_radialPath_lateralPart_prodMk hX hRm hR hZ hXZ
  refine indepFun_prodMk_right_of_indepFun_prodMk (hL.comp hX.measurable)
    (hRm.comp hX.measurable) hZ (hRA.comp measurable_id measurable_fst).symm ?_
  exact hXZ.comp (hL.prodMk hRm) measurable_id

/-- Replacing the inner radial path by an independent continuous path yields
a two-sided path independent of the lateral field. -/
theorem IsWholePlaneGFF.indepFun_lateralPart_twoSided
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hW : Measurable W) (hXW : IndepFun X W P) :
    IndepFun (fun ω => lateralPartC (X ω))
      (fun ω => twoSided (W ω)
        ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) P := by
  let rev : C(ℝ, ℝ) → C(ℝ≥0, ℝ) := fun r =>
    ⟨fun t => r (-(t : ℝ)), r.continuous.comp (by fun_prop)⟩
  have hrev : Measurable rev := ContinuousMap.measurable_iff_eval.2 fun t =>
    ContinuousMap.measurable_eval (-(t : ℝ))
  have hsplice : Measurable (fun p : C(ℝ, ℝ) × C(ℝ≥0, ℝ) =>
      twoSided p.2 (rev p.1)) :=
    measurable_twoSided.comp (measurable_snd.prodMk (hrev.comp measurable_fst))
  exact (IsWholePlaneGFF.indepFun_lateralPart_radialPath_prodMk hX hRm hR hW hXW).comp
    measurable_id hsplice

end LatticeProb.LQG
