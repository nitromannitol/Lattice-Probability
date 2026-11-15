import LatticeProb.LQG.CellWindowSideStrict
import LatticeProb.LQG.PeanosphereTimeChange
import LatticeProb.LQG.CoupledAreaTimeChange
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters

/-! # Clocked Peanosphere and strict shifted sides -/

set_option autoImplicit false

open MeasureTheory Set MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- A measurable reference-clock contour has the coupled Peanosphere structure
and, for an independent absolutely continuous phase, strict shifted sides. -/
theorem exists_coupled_clocked_peanosphere_strict
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hf : AEMeasurable (fun ω => coneField (X ω)
      (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω))) P)
    (ε : ℝ) (hε : 0 < ε) (Q : Measure ℝ) [SFinite Q] (hQ : Q ≪ volume) :
    ∃ G : Ω → Path2, Measurable G ∧
      (∀ᵐ ω ∂P, ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧
        (∀ t, η₀ ω t = η ω (ψ t)) ∧
        (∀ t, G ω t = bm ω (ψ t)) ∧
        (∀ t, CellScaling.JointScalingO.clock γ
          (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
          (η₀ ω) t = ψ t) ∧ RouteM.Peanosphere (G ω) (η₀ ω)) ∧
      ∀ᵐ p ∂P.prod Q, RouteM.SideStrict ε
        ⟨fun t => G p.1 (t + ε * p.2), (G p.1).continuous.comp (by fun_prop)⟩ := by
  obtain ⟨F, G, hF, hG, hclock, hstrict⟩ :=
    exists_coupled_clocked_brownian_strict_product hC hγ hf ε hε Q hQ
  refine ⟨G, hG, ?_, ?_⟩
  · filter_upwards [hclock, MoTInput.ae_peanosphere hC, hC.areaParam,
      MesoModel.FrozenIdentities.ae_exists_isVagueLimitC_cone hC hγ] with ω hw hp ha hv
    obtain ⟨ψ, hψ0, hcurve, _, hGψ⟩ := hw
    obtain ⟨μ, hμ⟩ := hv
    have hs0 : ψ.symm 0 = 0 := by rw [OrderIso.symm_apply_eq, hψ0]
    have hcurve' : (fun u => η₀ ω (ψ.symm u)) = (η ω : ℝ → ℂ) := by
      funext u
      rw [hcurve, ψ.apply_symm_apply]
    have harea : ∀ s t : ℝ, s ≤ t → μ ((fun u => η₀ ω (ψ.symm u)) '' Icc s t) =
        ENNReal.ofReal (t - s) := by
      rw [hcurve']
      exact ha.2 μ hμ
    have hclock' : ∀ t, CellScaling.JointScalingO.clock γ
        (coneField (X ω) (coneRadial γ γ (fun u => B u ω) (fun u => B' u ω)))
        (η₀ ω) t = ψ t := by
      intro t
      simpa only [OrderIso.symm_symm] using
        (CellScaling.JointScalingO.clock_eq hμ hs0 harea t)
    have hpath : G ω = ⟨fun t => bm ω (ψ t), (bm ω).continuous.comp ψ.continuous⟩ := by
      exact ContinuousMap.ext hGψ
    have hη : (η₀ ω : ℝ → ℂ) = fun t => η ω (ψ t) := funext hcurve
    refine ⟨ψ, hψ0, hcurve, hGψ, hclock', ?_⟩
    rw [hpath, hη]
    exact hp.comp_orderIso ψ
  · filter_upwards [hstrict] with p hp
    exact sideStrict_shift_of_cellWindowStrict (G p.1) hε hp

end LatticeProb
