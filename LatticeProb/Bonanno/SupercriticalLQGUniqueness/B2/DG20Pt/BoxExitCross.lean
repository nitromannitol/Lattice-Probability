/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.BoxExitCross at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CCross
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath

 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 




theorem min_four_exit_crossings_le_path
    (ξ : ℝ) (f : ℂ → ℝ) {P : ℝ → ℂ} {z w : ℂ}
    (hP : LQGMetric.IsPiecewiseC1Path P z w)
    {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ}
    (hx₀ : x₀ < x₁) (hx₃ : x₂ < x₃)
    (hy₀ : y₀ < y₁) (hy₃ : y₂ < y₃)
    (hin : P 0 ∈ Icc x₁ x₂ ×ℂ Icc y₁ y₂)
    (hout : P 1 ∉ Ioo x₀ x₃ ×ℂ Ioo y₀ y₃) :
    let K : Set ℂ := Icc x₀ x₃ ×ℂ Icc y₀ y₃
    let top := crossLenIn ξ f K (Icc x₀ x₃ ×ℂ {y₂}) (Icc x₀ x₃ ×ℂ {y₃})
    let bot := crossLenIn ξ f K (Icc x₀ x₃ ×ℂ {y₁}) (Icc x₀ x₃ ×ℂ {y₀})
    let right := crossLenIn ξ f K ({x₂} ×ℂ Icc y₀ y₃) ({x₃} ×ℂ Icc y₀ y₃)
    let left := crossLenIn ξ f K ({x₁} ×ℂ Icc y₀ y₃) ({x₀} ×ℂ Icc y₀ y₃)
    min (min top bot) (min right left) ≤ LQGMetric.lfppLen ξ f P := by
  dsimp
  obtain ⟨u, v, hu, huv, hv, hbox, hdir⟩ :=
    LQGMetric.DDDF.T20C.annulus_cross zero_le_one hP.continuousOn
      hx₀ hx₃ hy₀ hy₃ hin hout
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu, huv.le.trans hv⟩
  have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hu.trans huv.le, hv⟩
  have hK : ∀ t ∈ uIcc u v, P t ∈ Icc x₀ x₃ ×ℂ Icc y₀ y₃ := by
    intro t ht
    exact hbox t (by rwa [uIcc_of_le huv.le] at ht)
  rcases hdir with htop | hbot | hright | hleft
  · obtain ⟨huTop, hvTop, _⟩ := htop
    have hcross : crossLenIn ξ f (Icc x₀ x₃ ×ℂ Icc y₀ y₃)
        (Icc x₀ x₃ ×ℂ {y₂}) (Icc x₀ x₃ ×ℂ {y₃}) ≤
        LQGMetric.lfppLen ξ f P := by
      apply crossLenIn_le_of_sub hP huI hvI hK
      · rw [Complex.mem_reProdIm]
        exact ⟨(Complex.mem_reProdIm.mp (hbox u ⟨le_rfl, huv.le⟩)).1, huTop⟩
      · rw [Complex.mem_reProdIm]
        exact ⟨(Complex.mem_reProdIm.mp (hbox v ⟨huv.le, le_rfl⟩)).1, hvTop⟩
    exact (min_le_left _ _).trans ((min_le_left _ _).trans hcross)
  · obtain ⟨huBot, hvBot, _⟩ := hbot
    have hcross : crossLenIn ξ f (Icc x₀ x₃ ×ℂ Icc y₀ y₃)
        (Icc x₀ x₃ ×ℂ {y₁}) (Icc x₀ x₃ ×ℂ {y₀}) ≤
        LQGMetric.lfppLen ξ f P := by
      apply crossLenIn_le_of_sub hP huI hvI hK
      · rw [Complex.mem_reProdIm]
        exact ⟨(Complex.mem_reProdIm.mp (hbox u ⟨le_rfl, huv.le⟩)).1, huBot⟩
      · rw [Complex.mem_reProdIm]
        exact ⟨(Complex.mem_reProdIm.mp (hbox v ⟨huv.le, le_rfl⟩)).1, hvBot⟩
    exact (min_le_left _ _).trans ((min_le_right _ _).trans hcross)
  · obtain ⟨huRight, hvRight, _⟩ := hright
    have hcross : crossLenIn ξ f (Icc x₀ x₃ ×ℂ Icc y₀ y₃)
        ({x₂} ×ℂ Icc y₀ y₃) ({x₃} ×ℂ Icc y₀ y₃) ≤
        LQGMetric.lfppLen ξ f P := by
      apply crossLenIn_le_of_sub hP huI hvI hK
      · rw [Complex.mem_reProdIm]
        exact ⟨huRight, (Complex.mem_reProdIm.mp (hbox u ⟨le_rfl, huv.le⟩)).2⟩
      · rw [Complex.mem_reProdIm]
        exact ⟨hvRight, (Complex.mem_reProdIm.mp (hbox v ⟨huv.le, le_rfl⟩)).2⟩
    exact (min_le_right _ _).trans ((min_le_left _ _).trans hcross)
  · obtain ⟨huLeft, hvLeft, _⟩ := hleft
    have hcross : crossLenIn ξ f (Icc x₀ x₃ ×ℂ Icc y₀ y₃)
        ({x₁} ×ℂ Icc y₀ y₃) ({x₀} ×ℂ Icc y₀ y₃) ≤
        LQGMetric.lfppLen ξ f P := by
      apply crossLenIn_le_of_sub hP huI hvI hK
      · rw [Complex.mem_reProdIm]
        exact ⟨huLeft, (Complex.mem_reProdIm.mp (hbox u ⟨le_rfl, huv.le⟩)).2⟩
      · rw [Complex.mem_reProdIm]
        exact ⟨hvLeft, (Complex.mem_reProdIm.mp (hbox v ⟨huv.le, le_rfl⟩)).2⟩
    exact (min_le_right _ _).trans ((min_le_right _ _).trans hcross)

end SupercriticalLQGUniqueness.B2.DG20Pt
