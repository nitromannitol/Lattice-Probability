import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOMain
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OConeScale

/-! # Independence of the cone scale and the Lebesgue-time curve -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MatedCRTHarmonic
open scoped NNReal

namespace LatticeProb

/-- The cone scale has a positive measurable version independent of a measurable
transform of the Lebesgue-time curve. -/
theorem exists_coneScale_indepFun_curve
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (b : ℝ)
    {E : Type*} [MeasurableSpace E] (F : C(ℝ, ℂ) → E) (hF : Measurable F) :
    ∃ R : Ω → ℝ, Measurable R ∧ (∀ ω, 0 < R ω) ∧ IndepFun R (F ∘ ηL) P ∧
      (∀ᵐ ω ∂P, R ω = CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b) := by
  obtain ⟨W, hWm, _, hWη, hW⟩ :=
    CellScaling.JointScalingO.exists_radialPath_indepFun_curve D hγ0 hγ2
  let f : C(ℝ, ℝ) → ℝ := fun w => Real.exp
    (ConeScaling.lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b) w)
  have hfm : Measurable f := Real.measurable_exp.comp (ConeScaling.measurable_lastLevel _ _)
  refine ⟨f ∘ W, hfm.comp hWm, fun ω => Real.exp_pos _, ?_, ?_⟩
  · exact (hWη.comp measurable_snd hF).comp hfm measurable_id
  · filter_upwards [hW] with ω hω
    exact (IGLaw.coneScale_eq_exp_lastLevel_alpha γ γ b hω).symm

/-- The cone scale is almost everywhere measurable and independent of a
measurable transform of the Lebesgue-time curve. -/
theorem aemeasurable_indepFun_coneScale_curve
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (b : ℝ)
    {E : Type*} [MeasurableSpace E] (F : C(ℝ, ℂ) → E) (hF : Measurable F) :
    AEMeasurable (fun ω => CellScaling.coneScale γ γ (fun s => B s ω)
      (fun s => B' s ω) b) P ∧
    IndepFun (fun ω => CellScaling.coneScale γ γ (fun s => B s ω)
      (fun s => B' s ω) b) (F ∘ ηL) P := by
  obtain ⟨R, hRm, _, hRi, hReq⟩ := exists_coneScale_indepFun_curve D hγ0 hγ2 b F hF
  exact ⟨hRm.aemeasurable.congr hReq, hRi.congr hReq (ae_eq_refl _)⟩

end LatticeProb
