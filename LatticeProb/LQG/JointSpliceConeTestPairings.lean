import LatticeProb.LQG.JointSpliceConePairings

/-! # Joint cone observations and test pairings -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace LatticeProb.LQG

/-- The supported cone pairings, splice, local observations and path are
jointly independent of the observation under the splice hypotheses. -/
theorem joint_splice_observations_with_cone_pairings
    {Ω : Type} {ι κ A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
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
    (V : ι → Opens ℂ) (hV : ∀ i, V i ≤ ballO (0 : ℂ) 1)
    (ψ : κ → TestC) (hψ : ∀ i z, 1 < ‖z‖ → ψ i z = 0) :
    let G : Ω → DistC := fun ω => coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)
    let F : Ω → DistC := fun ω => GMSCase.addLogSing γ
      (replField X (fun ω => twoSided (W ω)
        ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω)
    IndepFun (fun ω => ((((F ω, lqgArea γ (F ω)),
      (fun i => (restrictTo (V i) (G ω), (lqgArea γ (G ω)).restrict (V i)))), W ω),
      fun i => G ω (ψ i))) Z P ∧
    ∀ᵐ ω ∂P, HasAreaLimitS γ (F ω) (lqgArea γ (F ω)) ∧
      (∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
        restrictTo U (G ω) = restrictTo U (F ω) ∧
        (lqgArea γ (G ω)).restrict U = (lqgArea γ (F ω)).restrict U) ∧
      ∀ (φ : TestC), (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
        G ω φ = replField X
          (fun ω => twoSided (W ω)
            ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω φ +
            ∫ z, φ z * (γ * (-Real.log ‖z‖)) := by
  obtain ⟨hi, he⟩ := joint_splice_observations_and_supported_pairings
    hγ hγ2 hX hB hB' hBB' hXB hRm hR hWm hWp hXW hW hZm hind V hV
  constructor
  · let T : ((DistC × Measure ℂ) × ((i : ι) → DistOn (V i) × Measure ℂ)) ×
        C(ℝ≥0, ℝ) →
        (((DistC × Measure ℂ) × ((i : ι) → DistOn (V i) × Measure ℂ)) ×
          C(ℝ≥0, ℝ)) × (κ → ℝ) :=
      fun p => (p, fun i => p.1.1.1 (ψ i))
    have hT : Measurable T := by
      refine measurable_id.prodMk (measurable_pi_iff.mpr fun i => ?_)
      exact (measurable_evalDist (ψ i)).comp
        (measurable_fst.comp (measurable_fst.comp measurable_fst))
    have hm := hi.comp hT measurable_id
    apply hm.congr _ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [he] with ω hω
    dsimp only [T, Function.comp_apply]
    apply Prod.ext
    · rfl
    · funext i
      change GMSCase.addLogSing γ (replField X
        (fun ω => twoSided (W ω)
          ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩) ω) (ψ i) =
        coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω) (ψ i)
      rw [hω.2.2 (ψ i) (hψ i), GMSCase.addLogSing, add_apply,
        ConeCirc.ofFunC_apply' (GMSCase.locallyIntegrable_logSing γ)]
      rfl
  · exact he

end LatticeProb.LQG
