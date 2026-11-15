import LatticeProb.LQG.CoupledAreaTimeChange
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.ClockMeasurable

/-! # Coupled area clocks from the reference field -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- The signed reference-area clock of the cone curve and its inverse recover
both directions of the time change between the coupled area curves. -/
theorem ae_zeroCone_coupled_clocks
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
      (∀ t, η₀ ω t = η ω (ψ t)) ∧
      (∀ t, CellScaling.JointScalingO.clock γ
        (coneField (X₀ ω) (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)))
        (η ω) t = ψ.symm t) ∧
      (∀ t, CellScaling.JointScalingO.timeOf γ
        (coneField (X₀ ω) (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)))
        (η ω) t = ψ t) := by
  filter_upwards [ae_zeroCone_curve_contour_clock hC, hC.areaParam₀,
    MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone₀ hC hγ] with ω hclock hpar hv
  obtain ⟨ψ, hψ0, hcurve, -, -⟩ := hclock
  obtain ⟨μ, hμ⟩ := hv
  have hcurve' : (fun u => η ω (ψ u)) = (η₀ ω : ℝ → ℂ) := by
    funext u
    exact (hcurve u).symm
  have harea : ∀ s t : ℝ, s ≤ t → μ ((fun u => η ω (ψ u)) '' Icc s t) =
      ENNReal.ofReal (t - s) := by
    rw [hcurve']
    exact hpar.2 μ hμ
  refine ⟨ψ, hψ0, hcurve, ?_, ?_⟩
  · intro t
    exact CellScaling.JointScalingO.clock_eq hμ hψ0 harea t
  · intro t
    exact CellScaling.JointScalingO.timeOf_eq hμ hψ0 harea t

set_option maxHeartbeats 400000 in
/-- Both signed reference-area clock coordinates are almost surely measurable. -/
theorem aemeasurable_zeroCone_coupled_clocks_at
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (t : ℝ) :
    AEMeasurable (fun ω => CellScaling.JointScalingO.clock γ
      (coneField (X₀ ω) (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)))
      (η ω) t) P ∧
    AEMeasurable (fun ω => CellScaling.JointScalingO.timeOf γ
      (coneField (X₀ ω) (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)))
      (η ω) t) P := by
  have hf : AEMeasurable (fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω))) P :=
    Canon.aemeasurable_reference_field hC hγ
  have hp : AEMeasurable (fun ω => (coneField (X₀ ω)
      (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω)), η ω)) P :=
    hf.prodMk hC.measurable_curves.2.1.aemeasurable
  constructor
  · simpa only [Function.comp_def] using
      (CellScaling.JointScalingO.measurable_clock γ t).comp_aemeasurable hp
  · simpa only [Function.comp_def] using
      (CellScaling.JointScalingO.measurable_timeOf γ t).comp_aemeasurable hp

end LatticeProb
