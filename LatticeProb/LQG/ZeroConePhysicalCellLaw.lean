import LatticeProb.LQG.ZeroConeShiftedCellLaw
import LatticeProb.LQG.ShiftedCellDilation

/-! # Scaling law for cells at a physical mesh -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped NNReal
open LQGMetric MatedCRTHarmonic

namespace LatticeProb

variable [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]

/-- The joint zero-cone law written using spatially rescaled cells at mesh `b`.
The phase is dimensionless, so its physical time shift is `b * θ`. -/
theorem zeroCone_physical_cells_law_prod
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {ν : Measure ℝ} [SFinite ν]
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
      (P.prod ν).map (fun p => (hb' p.1,
        (fun k : ℤ => NonemptyCompacts.map (fun z : ℂ => ((R p.1)⁻¹ : ℝ) * z)
          (continuous_const.mul continuous_id) (shiftedCompactCell (η₀ p.1) b p.2 k)), p.2)) =
      (P.prod ν).map (fun p => (h p.1,
        (fun k : ℤ => shiftedCompactCell (η₀ p.1) 1 p.2 k), p.2)) := by
  obtain ⟨W, hWm, hW, hlaw⟩ := zeroCone_shifted_cells_law_prod (ν := ν) hC hγ hb
  refine ⟨W, hWm, hW, ?_⟩
  dsimp only at hlaw ⊢
  convert hlaw using 1
  congr 1
  funext p
  congr 2
  funext k
  apply NonemptyCompacts.ext
  rw [NonemptyCompacts.coe_map]
  simpa only [mul_one] using
    (shiftedCompactCell_rescale (η₀ p.1)
      (CellScaling.coneRescaleCurve
        (Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) (γ⁻¹ * Real.log b) (W p.1))) b (η₀ p.1))
      (fun z : ℂ => ((Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ)
        (γ⁻¹ * Real.log b) (W p.1)))⁻¹ : ℝ) * z) b 1 p.2 (fun _ => rfl) k).symm

end LatticeProb
end
