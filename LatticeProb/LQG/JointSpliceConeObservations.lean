import LatticeProb.LQG.LocalConeObservations
import LatticeProb.LQG.NormalizedSpliceAreaIndependence

/-! # Joint observations of a splice and a local cone -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace LatticeProb.LQG

/-- The full splice field and area, the local cone observations, and the same
path are jointly independent of the observation under the splice hypotheses. -/
theorem joint_splice_and_local_cone_observations
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
      ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
        restrictTo U (G ω) = restrictTo U (F ω) ∧
        (lqgArea γ (G ω)).restrict U = (lqgArea γ (F ω)).restrict U := by
  obtain ⟨hglobal, _⟩ := normalized_splice_area_local_and_independent
    hγ hγ2 hX hB hB' hBB' hXB hRm hR hWm hWp hXW hW hZm hind
  obtain ⟨_, hevent⟩ := local_cone_observations_and_splice_agreement
    hγ hγ2 hX hB hB' hBB' hXB hRm hR hWm hWp hXW hW hZm hind V hV
  constructor
  · let T : (DistC × Measure ℂ) × C(ℝ≥0, ℝ) →
        ((DistC × Measure ℂ) × ((i : ι) → DistOn (V i) × Measure ℂ)) × C(ℝ≥0, ℝ) :=
      fun p => ((p.1, fun i => (restrictTo (V i) p.1.1, p.1.2.restrict (V i))), p.2)
    have hT : Measurable T := by
      apply Measurable.prodMk _ measurable_snd
      apply Measurable.prodMk measurable_fst
      apply measurable_pi_iff.mpr
      intro i
      exact ((measurable_restrictTo (V i)).comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_measure_restrict (V i : Set ℂ) (V i).2.measurableSet).comp
          (measurable_snd.comp measurable_fst))
    have hm := hglobal.comp hT measurable_id
    apply hm.congr _ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [hevent] with ω hω
    dsimp only [T, Function.comp_apply]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        have h := hω.2 (V i) (hV i)
        exact Prod.ext h.1.symm h.2.symm
    · rfl
  · exact hevent

end LatticeProb.LQG
