import LatticeProb.LQG.ZeroConeContinuousCurveLaw
import LatticeProb.LQG.MatingOfTreesCouplingBoundaryLength

/-! # Zero-cone field and continuous curve with an independent mark -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal
open LQGMetric MatedCRTHarmonic

namespace LatticeProb

/-- A separately sampled measurable mark can be adjoined to the joint law of
 the zero-cone field and its continuous area-parametrized curve. -/
theorem zeroCone_actual_continuous_curve_law_prod
    {γ : ℝ} {Ω Ξ E : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure Ξ} [SFinite ν] {θ : Ξ → E} (hθ : Measurable θ)
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
      (P.prod ν).map (fun p => ((hb' p.1,
        CellScaling.coneRescaleCurve (R p.1) b (η₀ p.1)), θ p.2)) =
      (P.prod ν).map (fun p => ((h p.1, η₀ p.1), θ p.2)) := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨W, hWm, hW, hlaw⟩ := zeroCone_actual_continuous_curve_law hC hγ hb
  refine ⟨W, hWm, hW, ?_⟩
  dsimp only at hlaw ⊢
  let y := γ⁻¹ * Real.log b
  let R : Ω → ℝ := fun ω => Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) y (W ω))
  have hR : Measurable R := Real.measurable_exp.comp
    ((ConeScaling.measurable_lastLevel (CellScaling.lqgQ γ) y).comp hWm)
  have hlat : Measurable (fun ω => CellScaling.lateralPart (X₀ ω)) :=
    ConeScaling.measurable_lateralPart.comp hC.gff₀.measurable
  have hfield : Measurable (fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω)) :=
    ConeScaling.measurable_fieldOf.comp (hlat.prodMk hWm)
  have hfieldb : Measurable (fun ω => ConeScaling.fieldOf
      (affineComp (R ω) 0 (CellScaling.lateralPart (X₀ ω)))
      (ConeScaling.radShift (CellScaling.lqgQ γ) y (W ω))) :=
    ConeScaling.measurable_fieldOf.comp
      ((MoTPort.ConeMeas.measurable_affineComp_joint.comp (hR.prodMk hlat)).prodMk
        ((ConeScaling.measurable_radShift (CellScaling.lqgQ γ) y).comp hWm))
  have hc : Measurable η₀ := hC.measurable_curves.2.2.1
  have hcb : Measurable (fun ω => CellScaling.coneRescaleCurve (R ω) b (η₀ ω)) :=
    (MatedCRT.measurable_coneRescaleCurve_uncurry b).comp (hR.prodMk hc)
  have hprod := congrArg (fun μ => μ.prod (ν.map θ)) hlaw
  rw [Measure.map_prod_map P ν (hfieldb.prodMk hcb) hθ,
    Measure.map_prod_map P ν (hfield.prodMk hc) hθ] at hprod
  exact hprod

end LatticeProb
