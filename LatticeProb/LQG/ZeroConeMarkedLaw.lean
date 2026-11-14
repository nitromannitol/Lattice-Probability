import LatticeProb.LQG.JointFieldCurveLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OCurveScale

/-! # Joint field and curve law for zero-cone radial scaling -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open LQGMetric
open MatedCRTHarmonic

namespace LatticeProb

/-- The shifted radial field and the unshifted field have the same joint law with
area-clock evaluations of the independently dilated curve. -/
theorem zeroCone_marked_radial_law
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (b : ℝ) :
    ∃ W : Ω → C(ℝ, ℝ), Measurable W ∧
      (∀ᵐ ω ∂P, ∀ t, W ω t = CellScaling.coneRadial γ 0
        (fun s => B₀ s ω) (fun s => B₀' s ω) t) ∧
      let y := γ⁻¹ * Real.log b
      let R : Ω → ℝ := fun ω => Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) y (W ω))
      let h : Ω → DistC := fun ω => ConeScaling.fieldOf (CellScaling.lateralPart (X₀ ω)) (W ω)
      let hb : Ω → DistC := fun ω => ConeScaling.fieldOf
        (affineComp (R ω) 0 (CellScaling.lateralPart (X₀ ω)))
        (ConeScaling.radShift (CellScaling.lqgQ γ) y (W ω))
      P.map (fun ω => (hb ω, fun t => CellScaling.JointScalingO.parEval γ (hb ω)
        (CellScaling.JointScalingO.dilCurve (R ω) (ηL ω)) t)) =
      P.map (fun ω => (h ω, fun t => CellScaling.JointScalingO.parEval γ (h ω) (ηL ω) t)) := by
  have : IsProbabilityMeasure P := hC.isProbabilityMeasure
  have hQ : 0 < CellScaling.lqgQ γ := IGLaw.lqgQ_pos' hγ.1
  have hind := IGLaw.IsMatingOfTreesCoupling.indepFun_ηL_coneData hC
  have hproj : Measurable fun q : MatedCRT.Field × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) × MatedCRT.Field ×
      (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => (q.2.2.2.1, (q.2.2.2.2.1, q.2.2.2.2.2)) := by
    fun_prop
  have hind₀ : IndepFun ηL (fun ω => (X₀ ω, ((fun t => B₀ t ω), (fun t => B₀' t ω)))) P :=
    hind.comp measurable_id hproj
  obtain ⟨W, hWm, hXW, hVη, hW⟩ := IGLaw.exists_radialPath_alpha (γ := γ) (α := 0)
    (by simpa using hQ) hC.bm_B₀ hC.bm_B₀' hC.indep_cone₀.1 hind₀
  refine ⟨W, hWm, hW, ?_⟩
  dsimp only
  let V : Ω → DistC × C(ℝ, ℝ) := fun ω => (X₀ ω, W ω)
  let y : ℝ := γ⁻¹ * Real.log b
  let R : DistC × C(ℝ, ℝ) → ℝ := fun v =>
    Real.exp (ConeScaling.lastLevel (CellScaling.lqgQ γ) y v.2)
  let F₁ : DistC × C(ℝ, ℝ) → DistC := fun v => ConeScaling.fieldOf
    (affineComp (R v) 0 (CellScaling.lateralPart v.1))
    (ConeScaling.radShift (CellScaling.lqgQ γ) y v.2)
  let F₂ : DistC × C(ℝ, ℝ) → DistC := fun v =>
    ConeScaling.fieldOf (CellScaling.lateralPart v.1) v.2
  have hV : Measurable V := hC.gff₀.measurable.prodMk hWm
  have hR : Measurable R := Real.measurable_exp.comp
    ((ConeScaling.measurable_lastLevel (CellScaling.lqgQ γ) y).comp measurable_snd)
  have hF₁ : Measurable F₁ := ConeScaling.measurable_fieldOf.comp
    ((MoTPort.ConeMeas.measurable_affineComp_joint.comp
      (hR.prodMk (ConeScaling.measurable_lateralPart.comp measurable_fst))).prodMk
      ((ConeScaling.measurable_radShift (CellScaling.lqgQ γ) y).comp measurable_snd))
  have hF₂ : Measurable F₂ := ConeScaling.measurable_fieldOf.comp
    ((ConeScaling.measurable_lateralPart.comp measurable_fst).prodMk measurable_snd)
  have hrad := IGLaw.map_radShift_coneRadial_alpha (γ := γ) (α := 0) hQ hC.bm_B₀ hC.bm_B₀'
    hC.indep_cone₀.2 hWm hW y
  have hlaw : P.map (fun ω => F₁ (V ω)) = P.map (fun ω => F₂ (V ω)) :=
    ConeScaling.map_fieldOf_shift_eq hC.gff₀ hWm hXW.symm hrad
  have hdil : ∀ r : ℝ, 0 < r →
      P.map (fun ω => CellScaling.JointScalingO.dilCurve r (ηL ω)) = P.map ηL := by
    intro r hr
    rw [← IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL hC 0 hr 0]
    apply Measure.map_congr
    filter_upwards [IGLaw.IsMatingOfTreesCoupling.ae_rootTime_zero hC] with ω hω
    exact CellScaling.JointScalingO.dilCurve_eq_affineReroot r (ηL ω) hω
  exact map_field_curve_eq_of_dilation hV hC.measurable_curves.1 hVη hdil
    hF₁ hF₂ hlaw hR (fun _ => Real.exp_pos _) γ
    (Filter.Eventually.of_forall fun _ => rfl) (Filter.Eventually.of_forall fun _ => rfl)

end LatticeProb
