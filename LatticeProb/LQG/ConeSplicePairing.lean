import LatticeProb.LQG.ConeReplacementPairing
import LatticeProb.LQG.SpliceRadialIntegrability
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge

/-! # Cone and Brownian splice pairings -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling QuantumZipper

namespace LatticeProb.LQG

/-- On one common event, a cone and a radial replacement sharing the inner
Brownian path differ on the unit disk by the logarithmic singularity. -/
theorem ae_coneFieldOf_apply_eq_replField_twoSided_add_log
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (W V : Ω → C(ℝ≥0, ℝ)) (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) :
    ∀ᵐ ω ∂P, ∀ (φ : TestC), (∀ z : ℂ, 1 < ‖z‖ → φ z = 0) →
      coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω) φ =
        replField X (fun ω => twoSided (W ω) (V ω)) ω φ +
          ∫ z, φ z * (γ * (-Real.log ‖z‖)) := by
  have hA : MoTPort.IsConeProcess γ (QuantumZipper.Qc γ)
      (fun t ω => LQGCone.motConeRadial γ γ (fun s => B s ω) (fun s => B' s ω) t) P :=
    LQGCone.isConeProcess_motConeRadial hB hB' hBB'
  have hLI : ∀ᵐ ω ∂P, LocallyIntegrable
      (fun z : ℂ => coneRadial γ γ (fun t => B t ω) (fun t => B' t ω)
        (-Real.log ‖z‖)) volume := by
    filter_upwards [MoTPort.ConeArea4.ae_locallyIntegrable_coneProfile hA] with ω hω
    refine hω.congr (Filter.Eventually.of_forall fun z => ?_)
    have he := LQGCone.coneRadial_eq_Q_add_motConeRadial γ γ
      (fun t => B t ω) (fun t => B' t ω) (-Real.log ‖z‖)
    change coneRadial γ γ _ _ _ = QuantumZipper.Qc γ * _ + _ at he
    exact he.symm
  filter_upwards [hLI, ae_locallyIntegrable_radialW_twoSided hB W V hW,
    hW, hB.eval_zero_ae_eq_zero] with ω hcone hsplice hw hz
  intro φ hφ
  have hpath : ∀ t : ℝ, 0 ≤ t → twoSided (W ω) (V ω) t = B t.toNNReal ω := by
    intro t ht
    have hw0 : W ω 0 = 0 := (hw 0).trans hz
    rw [twoSided_apply, Real.toNNReal_of_nonpos (neg_nonpos.mpr ht), sub_self,
      add_zero, hw0, sub_zero, hw]
  exact coneFieldOf_apply_eq_replField_add_log γ (X ω) _ _ _ hcone hsplice hpath φ hφ

end LatticeProb.LQG
