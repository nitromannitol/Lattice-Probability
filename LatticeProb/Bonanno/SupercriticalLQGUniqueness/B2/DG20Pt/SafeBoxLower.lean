/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SafeBoxLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SafeBoxCover

 




set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

def boxCrossMin (ξ : ℝ) (f : ℂ → ℝ) (c : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  let x₀ := c.re - 3 * ρ
  let x₁ := c.re - ρ
  let x₂ := c.re + ρ
  let x₃ := c.re + 3 * ρ
  let y₀ := c.im - 3 * ρ
  let y₁ := c.im - ρ
  let y₂ := c.im + ρ
  let y₃ := c.im + 3 * ρ
  let K : Set ℂ := Icc x₀ x₃ ×ℂ Icc y₀ y₃
  let top := crossLenIn ξ f K (Icc x₀ x₃ ×ℂ {y₂}) (Icc x₀ x₃ ×ℂ {y₃})
  let bot := crossLenIn ξ f K (Icc x₀ x₃ ×ℂ {y₁}) (Icc x₀ x₃ ×ℂ {y₀})
  let right := crossLenIn ξ f K ({x₂} ×ℂ Icc y₀ y₃) ({x₃} ×ℂ Icc y₀ y₃)
  let left := crossLenIn ξ f K ({x₁} ×ℂ Icc y₀ y₃) ({x₀} ×ℂ Icc y₀ y₃)
  min (min top bot) (min right left)

 



theorem exists_finite_box_cross_lower
    (U : TopologicalSpace.Opens ℂ) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hK₁U : K₁ ⊆ U) (hdisj : Disjoint K₁ K₂) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ F : Finset ℂ,
      ∀ ξ : ℝ, ∀ f : ℂ → ℝ,
        (⨅ c ∈ F, boxCrossMin ξ f c ρ) ≤ crossLenIn ξ f U K₁ K₂ := by
  obtain ⟨ρ, hρ, F, _hFsub, hcover, hsafe⟩ :=
    exists_finite_safe_box_cover U K₁ K₂ hK₁ hK₂ hK₁U hdisj
  refine ⟨ρ, hρ, F, ?_⟩
  intro ξ f
  apply le_crossLenIn
  intro P hP
  obtain ⟨z, hz, w, hw, hPc, _hPU⟩ := hP
  obtain ⟨c, hcF, hzinner⟩ := hcover z hz
  have hwout : P 1 ∉ Ioo (c.re - 3 * ρ) (c.re + 3 * ρ) ×ℂ
      Ioo (c.im - 3 * ρ) (c.im + 3 * ρ) := by
    rw [hPc.target]
    intro hwin
    have hwclosed : w ∈ Icc (c.re - 3 * ρ) (c.re + 3 * ρ) ×ℂ
        Icc (c.im - 3 * ρ) (c.im + 3 * ρ) := by
      rw [Complex.mem_reProdIm] at hwin ⊢
      exact ⟨Ioo_subset_Icc_self hwin.1, Ioo_subset_Icc_self hwin.2⟩
    exact (hsafe c hcF).2.ne_of_mem hwclosed hw rfl
  have hcross : boxCrossMin ξ f c ρ ≤ LQGMetric.lfppLen ξ f P := by
    simpa only [boxCrossMin] using
      (min_four_exit_crossings_le_path ξ f hPc
        (by linarith [hρ]) (by linarith [hρ])
        (by linarith [hρ]) (by linarith [hρ])
        (by simpa only [hPc.source] using hzinner) hwout)
  exact (iInf₂_le c hcF).trans hcross

end SupercriticalLQGUniqueness.B2.DG20Pt
