import LatticeProb.LQG.ZeroConeContinuousCurveMarkLaw
import LatticeProb.Topology.RandomShiftedCellComponentCount

/-! # Scaling law for intersection component counts -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped NNReal
open LQGMetric MatedCRTHarmonic

namespace LatticeProb

/-- The field, curve, phase and all intersection-component counts retain their
joint law under zero-cone scaling, for a finite independent phase law. -/
theorem zeroCone_component_counts_law_prod
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
          ((shiftedCompactCell (CellScaling.coneRescaleCurve (R p.1) b (η₀ p.1)) 1 p.2 j : Set ℂ) ∩
            shiftedCompactCell (CellScaling.coneRescaleCurve (R p.1) b (η₀ p.1)) 1 p.2 k)).ncard)) =
      (P.prod ν).map (fun p => (((h p.1, η₀ p.1), p.2),
        fun j k : ℤ => (nonSingletonComponents
          ((shiftedCompactCell (η₀ p.1) 1 p.2 j : Set ℂ) ∩
            shiftedCompactCell (η₀ p.1) 1 p.2 k)).ncard)) := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  obtain ⟨W, hWm, hW, hlaw⟩ :=
    zeroCone_actual_continuous_curve_law_prod (ν := ν) measurable_id hC hγ hb
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
  let f : Ω × ℝ → (DistC × C(ℝ, ℂ)) × ℝ := fun p =>
    ((ConeScaling.fieldOf (CellScaling.lateralPart (X₀ p.1)) (W p.1), η₀ p.1), p.2)
  let g : Ω × ℝ → (DistC × C(ℝ, ℂ)) × ℝ := fun p =>
    ((ConeScaling.fieldOf (affineComp (R p.1) 0 (CellScaling.lateralPart (X₀ p.1)))
      (ConeScaling.radShift (CellScaling.lqgQ γ) y (W p.1)),
      CellScaling.coneRescaleCurve (R p.1) b (η₀ p.1)), p.2)
  have hf : Measurable f := ((hfield.comp measurable_fst).prodMk (hc.comp measurable_fst)).prodMk measurable_snd
  have hg : Measurable g := ((hfieldb.comp measurable_fst).prodMk (hcb.comp measurable_fst)).prodMk measurable_snd
  let μ := (P.prod ν).map f
  let F : ((DistC × C(ℝ, ℂ)) × ℝ) →
      ((DistC × C(ℝ, ℂ)) × ℝ) × (ℤ → ℤ → ℕ) := fun p =>
    (p, fun j k => (nonSingletonComponents
      ((shiftedCompactCell p.1.2 1 p.2 j : Set ℂ) ∩ shiftedCompactCell p.1.2 1 p.2 k)).ncard)
  let : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
  have hF : AEMeasurable F μ := by
    refine aemeasurable_id.prodMk ?_
    exact aemeasurable_shifted_cell_component_ncard_array_of_ae
      (fun p : (DistC × C(ℝ, ℂ)) × ℝ => p.1.2) (fun _ => 1) (fun p => p.2) μ
      (measurable_snd.comp measurable_fst).aemeasurable aemeasurable_const measurable_snd.aemeasurable
  have hmaps : (P.prod ν).map g = μ := hlaw
  calc
    _ = ((P.prod ν).map g).map F :=
      (AEMeasurable.map_map_of_aemeasurable (hmaps ▸ hF) hg.aemeasurable).symm
    _ = μ.map F := congrArg (fun m => m.map F) hmaps
    _ = _ := AEMeasurable.map_map_of_aemeasurable hF hf.aemeasurable

end LatticeProb
end
