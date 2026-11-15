import LatticeProb.LQG.NormalizedRadialSplice
import LatticeProb.LQG.LogSingularArea
import LatticeProb.LQG.ConeSpliceLocalArea
import LatticeProb.LQG.ConeSpliceLocalLimit

/-! # Area of a normalized radial splice -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling MatedCRTHarmonic.LQGCoord
open QuantumZipper

namespace LatticeProb.LQG

/-- The logarithmically shifted normalized splice has a global continuum area
limit, which agrees locally with the area of the cone using the same path. -/
theorem ae_normalized_splice_area_and_cone_restrict
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
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
    (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) :
    let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
    let F : Ω → DistC := fun ω => GMSCase.addLogSing γ
      (replField X (fun ω => twoSided (W ω) (V ω)) ω)
    ∀ᵐ ω ∂P, HasAreaLimitS γ (F ω) (lqgArea γ (F ω)) ∧
      ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
        (lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω)
          (fun t => B' t ω))).restrict U = (lqgArea γ (F ω)).restrict U := by
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  let F : Ω → DistC := fun ω => GMSCase.addLogSing γ
    (replField X (fun ω => twoSided (W ω) (V ω)) ω)
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  have hnorm := LatticeProb.LQG.IsWholePlaneGFF.normalized_replField_twoSided hX hRm hR hWm hWp hXW
  have hex := ae_hasAreaLimitS_addLogSing hnorm.1 hγ hγ2
  have hcont : ∀ᵐ ω ∂P, HasAreaLimitS γ (F ω) (lqgArea γ (F ω)) := by
    filter_upwards [hex] with ω ⟨μ, hμ⟩
    have heq := lqgArea_eq_of_hasAreaLimitS hμ
    simpa only [F, V, heq] using hμ
  have hdyad : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ (F ω)) (lqgArea γ (F ω)) := by
    filter_upwards [hcont] with ω hω
    exact ⟨hω.1, fun f hf hfc => (hω.2 f hf hfc).comp tendsto_dyadicScale⟩
  have hcone := LQGCone.ae_lqgArea_vagueLimitC_coneField hγ hγ2
    (sub_pos.mp (CellScaling.lqgQ_sub_pos hγ hγ2)) hX hB hB' hBB'
    (ConeScaling.indepFun_motConeRadial hγ hγ2 hB hB' hXB)
  have hlocal := ae_coneFieldOf_splice_vagueLimit_restrict_eq hB hB' hBB' W V hW
    (fun ω => lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)))
    (fun ω => lqgArea γ (F ω)) hcone hdyad
  filter_upwards [hcont, hlocal] with ω hcontω hlocalω
  exact ⟨hcontω, hlocalω⟩

end LatticeProb.LQG
