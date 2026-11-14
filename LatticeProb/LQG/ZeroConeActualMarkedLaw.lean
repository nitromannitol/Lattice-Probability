import LatticeProb.LQG.ZeroConeMarkedLaw
import LatticeProb.LQG.ZeroConeAreaClock

/-! # Joint law of the zero-cone field and its area-parametrized curve -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal
open LQGMetric MatedCRTHarmonic

namespace LatticeProb

/-- At a fixed positive area scale, the rescaled zero-cone field and its
area-parametrized curve have the same joint law as the original pair. -/
theorem zeroCone_actual_marked_radial_law
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {b : ℝ} (hb : 0 < b) :
    ∃ W : Ω → C(ℝ, ℝ), Measurable W ∧
      (∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ 0
        (fun s => B₀ s ω) (fun s => B₀' s ω) t) ∧
      let y := γ⁻¹ * Real.log b
      let R : Ω → ℝ := fun ω => Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) y (W ω))
      let h : Ω → DistC := fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω)
      let hb' : Ω → DistC := fun ω => ConeScaling.fieldOf
        (affineComp (R ω) 0 (CellScaling.lateralPart (X₀ ω)))
        (ConeScaling.radShift (CellScaling.lqgQ γ) y (W ω))
      P.map (fun ω => (hb' ω, (⇑(CellScaling.coneRescaleCurve (R ω) b (η₀ ω)) : ℝ → ℂ))) =
      P.map (fun ω => (h ω, (⇑(η₀ ω) : ℝ → ℂ))) := by
  obtain ⟨W, hWm, hW, hlaw⟩ := zeroCone_marked_radial_law hC hγ b
  refine ⟨W, hWm, hW, ?_⟩
  have hclock := zeroCone_ae_area_clock hC hγ hb W hW
  dsimp only at hlaw ⊢
  calc
    _ = P.map (fun ω => (ConeScaling.fieldOf
          (affineComp (Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ)
            (γ⁻¹ * Real.log b) (W ω))) 0 (CellScaling.lateralPart (X₀ ω)))
          (ConeScaling.radShift (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b) (W ω)),
        fun t => CellScaling.JointScalingO.parEval γ (ConeScaling.fieldOf
          (affineComp (Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ)
            (γ⁻¹ * Real.log b) (W ω))) 0 (CellScaling.lateralPart (X₀ ω)))
          (ConeScaling.radShift (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b) (W ω)))
          (CellScaling.JointScalingO.dilCurve (Real.exp (ConeScaling.lastLevel
            (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b) (W ω))) (ηL ω)) t)) := by
      apply Measure.map_congr
      filter_upwards [hclock] with ω hω
      exact congrArg (fun c => (_, c)) hω.2
    _ = _ := hlaw.trans (Measure.map_congr (hclock.mono fun ω hω =>
      congrArg (fun c => (_, c)) hω.1)).symm

end LatticeProb
