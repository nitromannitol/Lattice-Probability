import LatticeProb.LQG.JointSpliceConeObservations
import LatticeProb.LQG.ConeSplicePairing

/-! # Joint cone observations and supported pairings -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace LatticeProb.LQG

/-- The joint observations retain a common event for all supported pairings
and all local field and area restrictions. -/
theorem joint_splice_observations_and_supported_pairings
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
    IndepFun (fun ω => (((F ω, lqgArea γ (F ω)),
      (fun i => (restrictTo (V i) (G ω), (lqgArea γ (G ω)).restrict (V i)))), W ω)) Z P ∧
    ∀ᵐ ω ∂P, HasAreaLimitS γ (F ω) (lqgArea γ (F ω)) ∧
      (∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
        restrictTo U (G ω) = restrictTo U (F ω) ∧
        (lqgArea γ (G ω)).restrict U = (lqgArea γ (F ω)).restrict U) ∧
      ∀ (φ : TestC), (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
        G ω φ = replField X
          (fun ω => twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω φ +
            ∫ z, φ z * (γ * (-Real.log ‖z‖)) := by
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  obtain ⟨hi, he⟩ := joint_splice_and_local_cone_observations
    hγ hγ2 hX hB hB' hBB' hXB hRm hR hWm hWp hXW hW hZm hind V hV
  refine ⟨hi, ?_⟩
  have hp := ae_coneFieldOf_apply_eq_replField_twoSided_add_log (γ := γ) (X := X) hB hB' hBB' W
    (fun ω => ⟨fun t => R (X ω) (-(t : ℝ)),
      (R (X ω)).continuous.comp (by fun_prop)⟩) hW
  filter_upwards [he, hp] with ω he hp
  exact ⟨he.1, he.2, hp⟩

end LatticeProb.LQG
