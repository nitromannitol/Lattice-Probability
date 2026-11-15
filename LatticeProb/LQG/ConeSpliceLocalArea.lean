import LatticeProb.LQG.ConeSpliceRestriction
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Events

/-! # Local area of a cone and a radial splice -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling QuantumZipper

namespace LatticeProb.LQG

/-- Global vague limits of a cone and the corresponding log-shifted radial
splice have equal restrictions to every open subset of the unit disk. -/
theorem ae_coneFieldOf_splice_vagueLimit_restrict_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (W V : Ω → C(ℝ≥0, ℝ)) (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω)
    (μ ν : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) (μ ω))
    (hν : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (GMSCase.addLogSing γ (replField X (fun ω => twoSided (W ω) (V ω)) ω))) (ν ω)) :
    ∀ᵐ ω ∂P, ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
      (μ ω).restrict U = (ν ω).restrict U := by
  filter_upwards [ae_restrictTo_coneFieldOf_eq_replField_twoSided_addLogSing
    hB hB' hBB' W V hW, hμ, hν] with ω hfield hcone hsplice
  intro U hU
  exact (GMS4FO.isVagueLimitOn_eq_restrict (hfield U hU).symm hcone
    (GMS4FO.isVagueLimitOn_restrict_of_global hsplice U)).symm

end LatticeProb.LQG
