import LatticeProb.LQG.AreaCurveContourClock
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FrozenIdentities
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOClock

/-! # Signed area clock between coupled curves -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- The signed area clock of the reference curve, measured in the cone field,
recovers the increasing time change between the two curves. -/
theorem ae_coupled_area_clock
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
      (∀ t, η₀ ω t = η ω (ψ t)) ∧
      ∀ t, CellScaling.JointScalingO.clock γ
        (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
        (η₀ ω) t = ψ t := by
  filter_upwards [ae_zeroCone_curve_contour_clock hC, hC.areaParam,
    MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone hC hγ] with ω hclock hpar hv
  obtain ⟨ψ, hψ0, hcurve, -, -⟩ := hclock
  obtain ⟨μ, hμ⟩ := hv
  have hs0 : ψ.symm 0 = 0 := by
    rw [OrderIso.symm_apply_eq, hψ0]
  have hcurve' : (fun u => η₀ ω (ψ.symm u)) = (η ω : ℝ → ℂ) := by
    funext u
    rw [hcurve, ψ.apply_symm_apply]
  have harea : ∀ s t : ℝ, s ≤ t → μ ((fun u => η₀ ω (ψ.symm u)) '' Icc s t) =
      ENNReal.ofReal (t - s) := by
    rw [hcurve']
    exact hpar.2 μ hμ
  refine ⟨ψ, hψ0, hcurve, ?_⟩
  intro t
  simpa only [OrderIso.symm_symm] using
    (CellScaling.JointScalingO.clock_eq hμ hs0 harea t)

set_option maxHeartbeats 400000 in
/-- If the cone field is almost surely measurable, each evaluation of the
signed area clock is almost surely measurable. -/
theorem aemeasurable_coupled_area_clock_at
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P) (t : ℝ) :
    AEMeasurable (fun ω => CellScaling.JointScalingO.clock γ
      (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
      (η₀ ω) t) P := by
  have hp : AEMeasurable (fun ω => (coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)), η₀ ω)) P :=
    hf.prodMk hC.measurable_curves.2.2.1.aemeasurable
  simpa only [Function.comp_def] using
    (CellScaling.JointScalingO.measurable_clock γ t).comp_aemeasurable hp

end LatticeProb
