import LatticeProb.LQG.ConeSplicePairing
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.ConeLaw

/-! # Restrictions of a cone and a radial splice -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling QuantumZipper

namespace LatticeProb.LQG

/-- A cone and a radial replacement with the same inner Brownian path agree
on every open subset of the unit disk after adding the logarithmic singularity. -/
theorem ae_restrictTo_coneFieldOf_eq_replField_twoSided_addLogSing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hBB' : IndepFun (pathOf B) (pathOf B') P)
    (W V : Ω → C(ℝ≥0, ℝ)) (hW : ∀ᵐ ω ∂P, ∀ t, W ω t = B t ω) :
    ∀ᵐ ω ∂P, ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ ball 0 1 →
      restrictTo U (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) =
      restrictTo U (GMSCase.addLogSing γ (replField X (fun ω => twoSided (W ω) (V ω)) ω)) := by
  filter_upwards [ae_coneFieldOf_apply_eq_replField_twoSided_add_log hB hB' hBB' W V hW] with ω hω
  intro U hU
  refine DFunLike.ext _ _ fun φ => ?_
  let ψ : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ
  have hψ : ∀ z : ℂ, 1 < ‖z‖ → ψ z = 0 := by
    intro z hz
    have hzU : z ∉ (U : Set ℂ) := by
      intro hz'
      have hzball := hU hz'
      rw [mem_ball, dist_zero_right] at hzball
      exact (not_lt_of_ge hz.le) hzball
    have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport fun hs => hzU (φ.tsupport_subset hs)
    simpa [ψ, TestFunction.monoCLM_apply] using hzero
  change coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω) ψ =
    GMSCase.addLogSing γ (replField X (fun ω => twoSided (W ω) (V ω)) ω) ψ
  rw [hω ψ hψ, GMSCase.addLogSing, add_apply,
    ConeCirc.ofFunC_apply' (GMSCase.locallyIntegrable_logSing γ)]
  rfl

end LatticeProb.LQG
