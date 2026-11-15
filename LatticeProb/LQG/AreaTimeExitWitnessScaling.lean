import LatticeProb.Topology.FirstExitBallDilation
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Theorem44

/-! # Area-time scaling of first-exit witnesses -/

set_option autoImplicit false

open Set Metric

namespace LatticeProb

/-- Positive area-time normalization transports both centered first-exit
ball witnesses from radius `s` to radius one. -/
theorem areaTimeScale_joint_exit_ball_witnesses
    (η : C(ℝ, ℂ)) {s : ℝ} (hs : 0 < s) (ρ δ : ℝ) :
    let f := MatedCRTHarmonic.GMS4b.curveRescale s (s ^ 2) η
    ((∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      f '' Icc (sSup {t : ℝ | t ≤ 0 ∧ f t ∉ ball 0 (1 : ℝ)}) 0) ∧
    (∃ z ∈ ball (0 : ℂ) ρ, ball z δ ⊆
      f '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ f t ∉ ball 0 (1 : ℝ)}))) ↔
    ((∃ z ∈ ball (0 : ℂ) (s * ρ), ball z (s * δ) ⊆
      η '' Icc (sSup {t : ℝ | t ≤ 0 ∧ η t ∉ ball 0 s}) 0) ∧
    (∃ z ∈ ball (0 : ℂ) (s * ρ), ball z (s * δ) ⊆
      η '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ η t ∉ ball 0 s}))) := by
  let e : ℝ ≃o ℝ := OrderIso.mulLeft₀ (s ^ 2) (pow_pos hs 2)
  have he : e 0 = 0 := by simp [e]
  have h := rooted_exit_ball_witnesses_smul_comp (η : ℝ → ℂ) e he
    (inv_pos.mpr hs) s (s * ρ) (s * δ)
  dsimp only at h ⊢
  have hf : (fun t => (s⁻¹ : ℝ) • η (e t)) =
      (MatedCRTHarmonic.GMS4b.curveRescale s (s ^ 2) η : ℝ → ℂ) := by
    funext t
    simp only [e, OrderIso.mulLeft₀_apply,
      MatedCRTHarmonic.GMS4b.curveRescale_apply, Complex.real_smul]
  have hfp (t : ℝ) : (s⁻¹ : ℝ) • η (e t) =
      MatedCRTHarmonic.GMS4b.curveRescale s (s ^ 2) η t := congrFun hf t
  simp_rw [hfp] at h
  simpa only [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul] using h

end LatticeProb
