import LatticeProb.LQG.ZeroConeComponentLaw
import LatticeProb.Topology.ShiftedCellComponentScaling

/-! # Physical-mesh intersection component counts under cone scaling -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped NNReal
open LQGMetric MatedCRTHarmonic

namespace LatticeProb

/-- A nonzero spatial dilation and time rescaling preserve shifted-cell
intersection component counts, with the physical mesh scaled by `b`. -/
theorem coneRescaleCurve_shifted_component_count
    (η : C(ℝ, ℂ)) {R : ℝ} (hR : R ≠ 0) (b θ : ℝ) (j k : ℤ) :
    (nonSingletonComponents
      ((shiftedCompactCell (CellScaling.coneRescaleCurve R b η) 1 θ j : Set ℂ) ∩
        shiftedCompactCell (CellScaling.coneRescaleCurve R b η) 1 θ k)).ncard =
    (nonSingletonComponents
      ((shiftedCompactCell η b θ j : Set ℂ) ∩ shiftedCompactCell η b θ k)).ncard := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ ((R⁻¹ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero hR))
  simpa only [nonSingletonComponents, mul_one] using
    (shifted_cell_inter_component_count_rescale η (CellScaling.coneRescaleCurve R b η)
      e b 1 θ (fun _ => rfl) j k)

/-- The zero-cone scaling law with the geometric component array expressed
using the original curve at physical mesh `b`. The phase is dimensionless. -/
theorem zeroCone_physical_component_counts_law_prod
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {ν : Measure ℝ} [IsFiniteMeasure ν]
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
      (P.prod ν).map (fun p => (((hb' p.1,
        CellScaling.coneRescaleCurve (R p.1) b (η₀ p.1)), p.2),
        fun j k : ℤ => (nonSingletonComponents
          ((shiftedCompactCell (η₀ p.1) b p.2 j : Set ℂ) ∩
            shiftedCompactCell (η₀ p.1) b p.2 k)).ncard)) =
      (P.prod ν).map (fun p => (((h p.1, η₀ p.1), p.2),
        fun j k : ℤ => (nonSingletonComponents
          ((shiftedCompactCell (η₀ p.1) 1 p.2 j : Set ℂ) ∩
            shiftedCompactCell (η₀ p.1) 1 p.2 k)).ncard)) := by
  obtain ⟨W, hWm, hW, hlaw⟩ := zeroCone_component_counts_law_prod (ν := ν) hC hγ hb
  refine ⟨W, hWm, hW, ?_⟩
  dsimp only at hlaw ⊢
  convert hlaw using 1
  congr 1
  funext p
  congr 2
  funext j k
  exact (coneRescaleCurve_shifted_component_count (η₀ p.1)
    (Real.exp_ne_zero _) b p.2 j k).symm

end LatticeProb
end
