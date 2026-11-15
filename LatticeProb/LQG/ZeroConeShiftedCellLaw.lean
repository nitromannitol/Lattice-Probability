import LatticeProb.LQG.ZeroConeContinuousCurveMarkLaw
import LatticeProb.Topology.CompactCurveRange

/-! # Joint scaling law of shifted zero-cone cells -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal
open LQGMetric MatedCRTHarmonic

namespace LatticeProb

variable [MeasurableSpace (TopologicalSpace.NonemptyCompacts ℂ)]
  [BorelSpace (TopologicalSpace.NonemptyCompacts ℂ)]

/-- The zero-cone field, independent phase, and all shifted cells have the
same joint law after a positive radial area rescaling. -/
theorem zeroCone_shifted_cells_law_prod
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
        (fun k : ℤ => shiftedCompactCell (CellScaling.coneRescaleCurve (R p.1) b (η₀ p.1)) 1 p.2 k), p.2)) =
      (P.prod ν).map (fun p => (h p.1,
        (fun k : ℤ => shiftedCompactCell (η₀ p.1) 1 p.2 k), p.2)) := by
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
  let F : (DistC × C(ℝ, ℂ)) × ℝ → DistC × (ℤ → TopologicalSpace.NonemptyCompacts ℂ) × ℝ :=
    fun p => (p.1.1, (fun k => shiftedCompactCell p.1.2 1 p.2 k), p.2)
  have hF : Measurable F := by
    refine (measurable_fst.comp measurable_fst).prodMk ?_
    refine (measurable_pi_iff.2 fun k => ?_).prodMk measurable_snd
    exact (measurable_shiftedCompactCell k).comp
      ((measurable_snd.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  have hsrc : Measurable (fun p : Ω × ℝ =>
      ((ConeScaling.fieldOf (CellScaling.lateralPart (X₀ p.1)) (W p.1), η₀ p.1), p.2)) :=
    ((hfield.comp measurable_fst).prodMk (hc.comp measurable_fst)).prodMk measurable_snd
  have hsrcb : Measurable (fun p : Ω × ℝ =>
      ((ConeScaling.fieldOf (affineComp (R p.1) 0 (CellScaling.lateralPart (X₀ p.1)))
        (ConeScaling.radShift (CellScaling.lqgQ γ) y (W p.1)),
        CellScaling.coneRescaleCurve (R p.1) b (η₀ p.1)), p.2)) :=
    ((hfieldb.comp measurable_fst).prodMk (hcb.comp measurable_fst)).prodMk measurable_snd
  calc
    _ = ((P.prod ν).map (fun p : Ω × ℝ =>
        ((ConeScaling.fieldOf (affineComp (R p.1) 0 (CellScaling.lateralPart (X₀ p.1)))
          (ConeScaling.radShift (CellScaling.lqgQ γ) y (W p.1)),
          CellScaling.coneRescaleCurve (R p.1) b (η₀ p.1)), p.2))).map F :=
      (Measure.map_map hF hsrcb).symm
    _ = ((P.prod ν).map (fun p : Ω × ℝ =>
        ((ConeScaling.fieldOf (CellScaling.lateralPart (X₀ p.1)) (W p.1), η₀ p.1), p.2))).map F :=
      congrArg (fun μ => μ.map F) hlaw
    _ = _ := Measure.map_map hF hsrc


end LatticeProb
end
