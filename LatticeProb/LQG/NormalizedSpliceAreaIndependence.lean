import LatticeProb.LQG.LogSingularAreaIndependence

/-! # Local cone area and independence of a normalized radial splice -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace LatticeProb.LQG

/-- The selected area of a logarithmic radial splice has a global limit,
agrees locally with the cone area, and retains the given joint independence. -/
theorem normalized_splice_area_local_and_independent
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
    let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
    let Y : Ω → DistC := replField X (fun ω => twoSided (W ω) (V ω))
    let F : Ω → DistC := fun ω => GMSCase.addLogSing γ (Y ω)
    IndepFun (fun ω => ((F ω, lqgArea γ (F ω)), W ω)) Z P ∧
    ∀ᵐ ω ∂P, HasAreaLimitS γ (F ω) (lqgArea γ (F ω)) ∧
      ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
        (lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω)
          (fun t => B' t ω))).restrict U = (lqgArea γ (F ω)).restrict U := by
  constructor
  · exact indepFun_logSingular_field_area_aux hγ hγ2
      (IsWholePlaneGFF.normalized_replField_twoSided hX hRm hR hWm hWp hXW).1 hWm hZm hind
  · exact ae_normalized_splice_area_and_cone_restrict hγ hγ2 hX hB hB' hBB' hXB
      hRm hR hWm hWp hXW hW

end LatticeProb.LQG
