import LatticeProb.LQG.LocalConeFieldAreaIndependence
import LatticeProb.LQG.LocalFieldAreaObservations

/-! # Local observations of a cone field and its area -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace LatticeProb.LQG

/-- Local field and area observations retain their joint independence with the
inner path, and agree simultaneously with the corresponding splice data. -/
theorem local_cone_observations_and_splice_agreement
    {Ω : Type} {ι A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {P : Measure Ω} {γ : ℝ} {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXB : IndepFun X (fun ω => (pathOf B ω, pathOf B' ω)) P)
    {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hWp : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P)
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    {Z : Ω → A} (hZm : Measurable Z)
    (hind : IndepFun (fun ω => (replField X
      (fun ω => twoSided (W ω)
        ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω,
        W ω)) Z P)
    (V : ι → Opens ℂ) (hV : ∀ i, V i ≤ ballO (0 : ℂ) 1) :
    let G : Ω → DistC := fun ω => coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)
    let F : Ω → DistC := fun ω => GMSCase.addLogSing γ
      (replField X (fun ω => twoSided (W ω)
        ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω)
    IndepFun (fun ω => ((fun i => (restrictTo (V i) (G ω),
      (lqgArea γ (G ω)).restrict (V i))), W ω)) Z P ∧
    ∀ᵐ ω ∂P, HasAreaLimitS γ (F ω) (lqgArea γ (F ω)) ∧
      ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
        restrictTo U (G ω) = restrictTo U (F ω) ∧
        (lqgArea γ (G ω)).restrict U = (lqgArea γ (F ω)).restrict U := by
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  constructor
  · exact indepFun_restricted_field_area_family V hV
      (indepFun_local_cone_field_area_path hγ hγ2 hX hB hB' hBB' hXB
        hRm hR hWm hWp hXW hW hZm hind)
  · have ha := ae_normalized_splice_area_and_cone_restrict hγ hγ2 hX hB hB'
      hBB' hXB hRm hR hWm hWp hXW hW
    have hf := ae_restrictTo_coneFieldOf_eq_replField_twoSided_addLogSing
      (γ := γ) (X := X) hB hB' hBB' W
      (fun ω => ⟨fun t => R (X ω) (-(t : ℝ)),
        (R (X ω)).continuous.comp (by fun_prop)⟩) hW
    filter_upwards [ha, hf] with ω haω hfω
    exact ⟨haω.1, fun U hU => ⟨hfω U hU, haω.2 U hU⟩⟩

end LatticeProb.LQG
