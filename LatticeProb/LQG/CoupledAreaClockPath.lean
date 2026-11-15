import LatticeProb.LQG.CoupledAreaTimeChange
import LatticeProb.Prob.IndepFunCountableCoordinates

/-! # A measurable continuous version of the coupled area clock -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- If the cone field is almost surely measurable, the signed area clock has a
measurable continuous-path version which almost surely agrees at all times
with a zero-preserving order isomorphism between the two area curves. -/
theorem exists_measurable_coupled_area_clock_path
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P) :
    ∃ F : Ω → C(ℝ, ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧ ∀ t, F ω t = ψ t := by
  classical
  let c : Ω → ℝ → ℝ := fun ω t => CellScaling.JointScalingO.clock γ
    (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
    (η₀ ω) t
  let F : Ω → C(ℝ, ℝ) := fun ω =>
    if h : ∃ ψ : ℝ ≃o ℝ, ∀ t, c ω t = ψ t then
      ⟨h.choose, h.choose.continuous⟩
    else 0
  have hclock : ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
      (∀ t, η₀ ω t = η ω (ψ t)) ∧ ∀ t, c ω t = ψ t :=
    ae_coupled_area_clock hC hγ
  have hF : ∀ᵐ ω ∂P, ∀ t, F ω t = c ω t := by
    filter_upwards [hclock] with ω hω
    obtain ⟨ψ, _, _, hψ⟩ := hω
    have hex : ∃ ψ : ℝ ≃o ℝ, ∀ t, c ω t = ψ t := ⟨ψ, hψ⟩
    intro t
    simp only [F, dite_eq_left hex, ContinuousMap.coe_mk]
    exact (hex.choose_spec t).symm
  have hcoord : AEMeasurable (fun ω (q : ℚ) => F ω (q : ℝ)) P := by
    apply AEMeasurable.of_eval
    intro q
    apply (aemeasurable_coupled_area_clock_at hC hf (q : ℝ)).congr
    filter_upwards [hF] with ω hω
    exact (hω (q : ℝ)).symm
  have hemb := Prob.measurableEmbedding_restrict_denseRange
    (T := ℝ) (ι := ℚ) (D := fun q : ℚ => (q : ℝ)) Rat.denseRange_cast
  have hFm : AEMeasurable F P := hemb.aemeasurable_comp_iff.mp hcoord
  refine ⟨hFm.mk F, hFm.measurable_mk, ?_⟩
  filter_upwards [hclock, hF, hFm.ae_eq_mk] with ω hω hωF hmk
  obtain ⟨ψ, hψ0, hcurve, hψ⟩ := hω
  refine ⟨ψ, hψ0, hcurve, ?_⟩
  intro t
  rw [← hmk, hωF t, hψ t]

end LatticeProb
