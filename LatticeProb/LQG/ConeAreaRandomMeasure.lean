import LatticeProb.LQG.AreaReparamMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.ConeLocal
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.RadialPath

/-! # Measurability of cone area measures

The subcritical cone area measure is an almost everywhere measurable random
measure, obtained from the dyadic approximations of the cone field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open LQGMetric MatedCRTHarmonic

namespace LatticeProb

/-- A vague limit of the dyadic area approximations of an almost everywhere
measurable random field is an almost everywhere measurable random measure. -/
theorem aemeasurable_lqgArea_of_ae_vagueLimit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} {H : Ω → DistC}
    (hH : AEMeasurable H P)
    (hlim : ∀ᵐ ω ∂P, ∃ μ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (H ω)) μ) :
    AEMeasurable (fun ω => CellScaling.lqgArea γ (H ω)) P := by
  let H₀ := hH.mk H
  have hH₀ : Measurable H₀ := hH.measurable_mk
  have heq : H =ᵐ[P] H₀ := hH.ae_eq_mk
  have hlim₀ : ∀ᵐ ω ∂P, ∃ μ, CellScaling.IsVagueLimitC
      (CellScaling.lqgAreaApprox γ (H₀ ω)) μ := by
    filter_upwards [hlim, heq] with ω hω hωeq
    simpa only [← hωeq] using hω
  have hmeas : ∀ k (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      Measurable fun ω => ∫ z, f z ∂(CellScaling.lqgAreaApprox γ (H₀ ω) k) := by
    intro k f hf _
    exact (LQG.measurable_integral_lqgAreaApprox γ k hf.measurable).comp hH₀
  have harea : AEMeasurable (fun ω => CellScaling.lqgArea γ (H₀ ω)) P := by
    exact VagueLimit.aemeasurable_vagueLimitOrZero hmeas hlim₀
  apply harea.congr
  filter_upwards [heq] with ω hω
  rw [hω]

/-- The area measure associated with the subcritical γ-cone field is an almost
everywhere measurable random measure. -/
theorem aemeasurable_gammaConeArea
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P)
    (hBB : ProbabilityTheory.IndepFun (QuantumZipper.pathOf B) (QuantumZipper.pathOf B') P)
    (hXB : ProbabilityTheory.IndepFun X (fun ω => (QuantumZipper.pathOf B ω,
      QuantumZipper.pathOf B' ω)) P) :
    AEMeasurable (fun ω => CellScaling.lqgArea γ
      (CellScaling.coneField (X ω)
        (CellScaling.coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) P := by
  let : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  apply aemeasurable_lqgArea_of_ae_vagueLimit
  · exact GMSCM.aemeasurable_coneFieldOf hX hB hB' hBB
  · have hlim := LQGCone.ae_lqgArea_vagueLimitC_coneField hγ hγ2
      (sub_pos.mp (CellScaling.lqgQ_sub_pos hγ hγ2)) hX hB hB' hBB
      (ConeScaling.indepFun_motConeRadial hγ hγ2 hB hB' hXB)
    filter_upwards [hlim] with ω hω
    exact ⟨_, hω⟩

end LatticeProb
