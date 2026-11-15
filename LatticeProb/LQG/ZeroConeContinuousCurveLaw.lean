import LatticeProb.LQG.ZeroConeActualMarkedLaw
import LatticeProb.Probability.MapRestrictSubtype

/-! # Scaling law of the zero-cone field and continuous curve -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal
open LQGMetric MatedCRTHarmonic

namespace LatticeProb

open Classical

private theorem measurable_restrict_continuousCurve {α : Type*} [MeasurableSpace α] :
    Measurable ({p : α × (ℝ → ℂ) | Continuous p.2}.domRestrict
      fun p => (p.1, if hc : Continuous p.2 then (⟨p.2, hc⟩ : C(ℝ, ℂ)) else 0)) := by
  have heq : ({p : α × (ℝ → ℂ) | Continuous p.2}.domRestrict
      fun p => (p.1, if hc : Continuous p.2 then (⟨p.2, hc⟩ : C(ℝ, ℂ)) else 0)) =
      fun x => (x.1.1, (⟨x.1.2, x.2⟩ : C(ℝ, ℂ))) := by
    funext x
    have hx : Continuous x.1.2 := x.2
    simp only [Set.domRestrict, hx, ↓reduceDIte]
  rw [heq]
  refine (measurable_fst.comp measurable_subtype_coe).prodMk ?_
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  exact (measurable_pi_apply t).comp (measurable_snd.comp measurable_subtype_coe)

/-- The zero-cone field and its continuous area-parametrized curve have the same
joint law after scaling by any positive area factor. -/
theorem zeroCone_actual_continuous_curve_law
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
      P.map (fun ω => (hb' ω, CellScaling.coneRescaleCurve (R ω) b (η₀ ω))) =
      P.map (fun ω => (h ω, η₀ ω)) := by
  obtain ⟨W, hWm, hW, hlaw⟩ := zeroCone_actual_marked_radial_law hC hγ hb
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
  have hc : Measurable (fun ω => (⇑(η₀ ω) : ℝ → ℂ)) :=
    CellScaling.JointScalingO.measurable_coe_continuousMap_complex.comp hC.measurable_curves.2.2.1
  have hcb : Measurable (fun ω => (⇑(CellScaling.coneRescaleCurve (R ω) b (η₀ ω)) : ℝ → ℂ)) := by
    apply measurable_pi_iff.2
    intro t
    change Measurable (fun ω => (((R ω)⁻¹ : ℝ) : ℂ) * η₀ ω (b * t))
    have hη := (ContinuousMap.measurable_eval (b * t)).comp hC.measurable_curves.2.2.1
    fun_prop
  have key := map_comp_eq_of_map_eq_of_ae_mem (hfieldb.prodMk hcb).aemeasurable
    (hfield.prodMk hc).aemeasurable hlaw
    (ae_of_all _ fun ω => (CellScaling.coneRescaleCurve (R ω) b (η₀ ω)).continuous)
    (ae_of_all _ fun ω => (η₀ ω).continuous) (measurable_restrict_continuousCurve (α := DistC))
  refine (congrArg (fun F => P.map F) ?_).trans (key.trans (congrArg (fun F => P.map F) ?_))
  · funext ω
    have hc : Continuous (⇑(CellScaling.coneRescaleCurve (R ω) b (η₀ ω)) : ℝ → ℂ) :=
      (CellScaling.coneRescaleCurve (R ω) b (η₀ ω)).continuous
    refine Prod.ext rfl ?_
    simp [hc]
    ext t
    rfl
  · funext ω
    have hc : Continuous (⇑(η₀ ω) : ℝ → ℂ) := (η₀ ω).continuous
    refine Prod.ext rfl ?_
    simp [hc]
    ext t
    rfl

end LatticeProb
