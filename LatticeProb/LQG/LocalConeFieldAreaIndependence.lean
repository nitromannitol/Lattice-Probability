import LatticeProb.LQG.LocalConeAreaIndependence

/-! # Joint independence of a local cone field and area -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace LatticeProb.LQG

/-- The local cone field, its local area and the inner path are jointly
independent of the given observation under the splice independence hypotheses. -/
theorem indepFun_local_cone_field_area_path
    {Ω : Type} {A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {P : Measure Ω} {γ : ℝ}
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
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
        W ω)) Z P) :
    IndepFun (fun ω => ((restrictTo (ballO (0 : ℂ) 1)
      (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
      (lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω)
        (fun t => B' t ω))).restrict (ball 0 1)), W ω)) Z P := by
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  let F : Ω → DistC := fun ω => GMSCase.addLogSing γ
    (replField X (fun ω => twoSided (W ω) (V ω)) ω)
  have hjoint := indepFun_normalized_splice_and_local_cone_area
    hγ hγ2 hX hB hB' hBB' hXB hRm hR hWm hWp hXW hW hZm hind
  have hmap : Measurable (fun p : (DistC × Measure ℂ) × C(ℝ≥0, ℝ) =>
      ((restrictTo (ballO (0 : ℂ) 1) p.1.1, p.1.2), p.2)) :=
    (((measurable_restrictTo _).comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hres := hjoint.comp hmap measurable_id
  have heq := ae_restrictTo_coneFieldOf_eq_replField_twoSided_addLogSing
    (γ := γ) (X := X) hB hB' hBB' W V hW
  apply hres.congr _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [heq] with ω hω
  have h := hω (ballO (0 : ℂ) 1) (Subset.rfl)
  change ((restrictTo (ballO (0 : ℂ) 1) (F ω), _), W ω) = _
  rw [h]

end LatticeProb.LQG
