import LatticeProb.LQG.ZeroConeCoupledClocks
import LatticeProb.Prob.IndepFunCountableCoordinates

/-! # Measurable paths for coupled area clocks -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

private theorem exists_measurable_path_of_orderIso_coordinates
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (c : Ω → ℝ → ℝ)
    (hc : ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ∀ t, c ω t = ψ t)
    (hm : ∀ t, AEMeasurable (fun ω => c ω t) P) :
    ∃ F : Ω → C(ℝ, ℝ), Measurable F ∧ ∀ᵐ ω ∂P, ∀ t, F ω t = c ω t := by
  classical
  let F : Ω → C(ℝ, ℝ) := fun ω =>
    if h : ∃ ψ : ℝ ≃o ℝ, ∀ t, c ω t = ψ t then
      ⟨h.choose, h.choose.continuous⟩
    else 0
  have hF : ∀ᵐ ω ∂P, ∀ t, F ω t = c ω t := by
    filter_upwards [hc] with ω hω
    intro t
    simp only [F, dite_eq_left hω, ContinuousMap.coe_mk]
    exact (hω.choose_spec t).symm
  have hcoord : AEMeasurable (fun ω (q : ℚ) => F ω (q : ℝ)) P := by
    apply AEMeasurable.of_eval
    intro q
    apply (hm (q : ℝ)).congr
    filter_upwards [hF] with ω hω
    exact (hω (q : ℝ)).symm
  have hemb := Prob.measurableEmbedding_restrict_denseRange
    (T := ℝ) (ι := ℚ) (D := fun q : ℚ => (q : ℝ)) Rat.denseRange_cast
  have hFm : AEMeasurable F P := hemb.aemeasurable_comp_iff.mp hcoord
  refine ⟨hFm.mk F, hFm.measurable_mk, ?_⟩
  filter_upwards [hF, hFm.ae_eq_mk] with ω hω hmk
  intro t
  rw [← hmk, hω t]

/-- Both directions of the coupled area time change have measurable continuous
versions. On one almost-sure event they agree with an order isomorphism and
its inverse, and the forward version is the signed cone-area clock. -/
theorem exists_measurable_zeroCone_coupled_clock_paths
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (hC : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ F G : Ω → C(ℝ, ℝ), Measurable F ∧ Measurable G ∧
      ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, F ω t = ψ t) ∧ (∀ t, G ω t = ψ.symm t) ∧
        ∀ t, F ω t = CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) t := by
  let c : Ω → ℝ → ℝ := fun ω t => CellScaling.JointScalingO.clock γ
    (coneField (X₀ ω) (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω))) (η ω) t
  let d : Ω → ℝ → ℝ := fun ω t => CellScaling.JointScalingO.timeOf γ
    (coneField (X₀ ω) (coneRadial γ 0 (fun u => B₀ u ω) (fun u => B₀' u ω))) (η ω) t
  have hclock := ae_zeroCone_coupled_clocks hC hγ
  have hc : ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ∀ t, c ω t = ψ t := by
    filter_upwards [hclock] with ω hω
    obtain ⟨ψ, _, _, hc, _⟩ := hω
    exact ⟨ψ.symm, hc⟩
  have hd : ∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ∀ t, d ω t = ψ t := by
    filter_upwards [hclock] with ω hω
    obtain ⟨ψ, _, _, _, hd⟩ := hω
    exact ⟨ψ, hd⟩
  obtain ⟨G, hGm, hG⟩ := exists_measurable_path_of_orderIso_coordinates c hc
    (fun t => (aemeasurable_zeroCone_coupled_clocks_at hC hγ t).1)
  obtain ⟨F, hFm, hF⟩ := exists_measurable_path_of_orderIso_coordinates d hd
    (fun t => (aemeasurable_zeroCone_coupled_clocks_at hC hγ t).2)
  refine ⟨F, G, hFm, hGm, ?_⟩
  filter_upwards [hclock, hF, hG, hC.areaParam,
    MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone hC hγ] with ω hω hFω hGω hpar hv
  obtain ⟨ψ, hψ0, hcurve, hcω, hdω⟩ := hω
  change ∀ t, d ω t = ψ t at hdω
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
  refine ⟨ψ, hψ0, hcurve, ?_, ?_, ?_⟩
  · intro t
    exact (hFω t).trans (hdω t)
  · intro t
    exact (hGω t).trans (hcω t)
  · intro t
    rw [hFω t, hdω t]
    symm
    simpa only [OrderIso.symm_symm] using
      (CellScaling.JointScalingO.clock_eq hμ hs0 harea t)

end LatticeProb
