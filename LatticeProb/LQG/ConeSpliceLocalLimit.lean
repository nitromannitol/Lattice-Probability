import LatticeProb.LQG.ConeSpliceRestriction
import LatticeProb.LQG.ConeAreaRandomMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.Cert

/-! # Local area limits of a radial splice -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling QuantumZipper

namespace LatticeProb.LQG

/-- The cone area restricted to an open subset of the unit disk is a local
vague limit for the logarithmically shifted splice with the same inner path. -/
theorem ae_splice_local_vagueLimit_coneArea
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (hXB : IndepFun X (fun ω => (pathOf B ω, pathOf B' ω)) P)
    (W V : Ω → C(ℝ≥0, ℝ)) (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) :
    ∀ᵐ ω ∂P, ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
      IsVagueLimitOn (U : Set ℂ) (lqgAreaApprox γ
        (GMSCase.addLogSing γ (replField X (fun ω => twoSided (W ω) (V ω)) ω)))
        ((lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))).restrict U) := by
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  have hlim := LQGCone.ae_lqgArea_vagueLimitC_coneField hγ hγ2
    (sub_pos.mp (CellScaling.lqgQ_sub_pos hγ hγ2)) hX hB hB' hBB'
    (ConeScaling.indepFun_motConeRadial hγ hγ2 hB hB' hXB)
  filter_upwards [ae_restrictTo_coneFieldOf_eq_replField_twoSided_addLogSing
    hB hB' hBB' W V hW, hlim] with ω hfield hcone
  intro U hU
  exact GMS4cM.isVagueLimitOn_of_restrictTo_eq (hfield U hU)
    (GMS4FO.isVagueLimitOn_restrict_of_global hcone U)

end LatticeProb.LQG
