import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOLaw

/-! # Joint laws of fields and area-parametrized curves -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric

namespace LatticeProb

/-- A random dilation of an independent curve preserves the joint law of the field and
its parametrized curve when the two fields have the same law. The two almost-sure
identities connect the abstract parametrizations to the observed field and curve. -/
theorem map_field_curve_eq_of_dilation
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Ω → β} {ηL : Ω → C(ℝ, ℂ)}
    (hV : Measurable V) (hηL : Measurable ηL) (hind : IndepFun V ηL P)
    (hdil : ∀ r : ℝ, 0 < r →
      P.map (fun ω => MatedCRTHarmonic.CellScaling.JointScalingO.dilCurve r (ηL ω)) =
        P.map ηL)
    {F₁ F₂ : β → DistC} (hF₁ : Measurable F₁) (hF₂ : Measurable F₂)
    (hlaw : P.map (fun ω => F₁ (V ω)) = P.map (fun ω => F₂ (V ω)))
    {R : β → ℝ} (hR : Measurable R) (hRpos : ∀ v, 0 < R v)
    (γ : ℝ) {h₁ h₂ : Ω → DistC} {c₁ c₂ : Ω → (ℝ → ℂ)}
    (he₁ : ∀ᵐ ω ∂P, (h₁ ω, c₁ ω) =
      (F₁ (V ω), fun t => MatedCRTHarmonic.CellScaling.JointScalingO.parEval γ
        (F₁ (V ω)) (MatedCRTHarmonic.CellScaling.JointScalingO.dilCurve (R (V ω)) (ηL ω)) t))
    (he₂ : ∀ᵐ ω ∂P, (h₂ ω, c₂ ω) =
      (F₂ (V ω), fun t => MatedCRTHarmonic.CellScaling.JointScalingO.parEval γ
        (F₂ (V ω)) (ηL ω) t)) :
    P.map (fun ω => (h₁ ω, c₁ ω)) = P.map (fun ω => (h₂ ω, c₂ ω)) := by
  let Ψ : DistC × C(ℝ, ℂ) → DistC × (ℝ → ℂ) := fun p =>
    (p.1, fun t => MatedCRTHarmonic.CellScaling.JointScalingO.parEval γ p.1 p.2 t)
  have hΨ : Measurable Ψ := measurable_fst.prodMk
    (measurable_pi_iff.2 fun t =>
      MatedCRTHarmonic.CellScaling.JointScalingO.measurable_parEval γ t)
  have hl : Measurable (fun ω => Ψ
      (F₁ (V ω), MatedCRTHarmonic.CellScaling.JointScalingO.dilCurve (R (V ω)) (ηL ω))) :=
    hΨ.comp (((hF₁.comp hV).prodMk
      (MatedCRTHarmonic.CellScaling.JointScalingO.measurable_dilCurve.comp
        (((hR.comp hV).prodMk hηL)))))
  have hr : Measurable (fun ω => Ψ (F₂ (V ω), ηL ω)) :=
    hΨ.comp ((hF₂.comp hV).prodMk hηL)
  calc
    P.map (fun ω => (h₁ ω, c₁ ω)) =
        P.map (fun ω => Ψ (F₁ (V ω),
          MatedCRTHarmonic.CellScaling.JointScalingO.dilCurve (R (V ω)) (ηL ω))) :=
      Measure.map_congr he₁
    _ = P.map (fun ω => Ψ (F₂ (V ω), ηL ω)) := by
      ext T hT
      rw [Measure.map_apply hl hT, Measure.map_apply hr hT]
      exact MatedCRTHarmonic.CellScaling.JointScalingO.measure_dilCurve_indep_eq
        hV hηL hind hdil hF₁ hF₂ hlaw hR hRpos hΨ hT
    _ = P.map (fun ω => (h₂ ω, c₂ ω)) := (Measure.map_congr he₂).symm

end LatticeProb
