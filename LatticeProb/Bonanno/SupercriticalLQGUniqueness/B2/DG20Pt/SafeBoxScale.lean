/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SafeBoxScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.BoundedLowerSubdomain
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale

 




set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

def scaledBoxCrossMin (ξ : ℝ) (g : ℂ → ℝ) (c : ℂ) (ρ r : ℝ) : ℝ≥0∞ :=
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  let x₀ := c.re - 3 * ρ
  let x₁ := c.re - ρ
  let x₂ := c.re + ρ
  let x₃ := c.re + 3 * ρ
  let y₀ := c.im - 3 * ρ
  let y₁ := c.im - ρ
  let y₂ := c.im + ρ
  let y₃ := c.im + 3 * ρ
  let K : Set ℂ := Icc x₀ x₃ ×ℂ Icc y₀ y₃
  let top := crossLenIn ξ g (F '' K)
    (F '' (Icc x₀ x₃ ×ℂ {y₂})) (F '' (Icc x₀ x₃ ×ℂ {y₃}))
  let bot := crossLenIn ξ g (F '' K)
    (F '' (Icc x₀ x₃ ×ℂ {y₁})) (F '' (Icc x₀ x₃ ×ℂ {y₀}))
  let right := crossLenIn ξ g (F '' K)
    (F '' ({x₂} ×ℂ Icc y₀ y₃)) (F '' ({x₃} ×ℂ Icc y₀ y₃))
  let left := crossLenIn ξ g (F '' K)
    (F '' ({x₁} ×ℂ Icc y₀ y₃)) (F '' ({x₀} ×ℂ Icc y₀ y₃))
  min (min top bot) (min right left)

 


theorem scaledBoxCrossMin_eq_mul (ξ : ℝ) (g : ℂ → ℝ) (c : ℂ)
    (ρ r : ℝ) (hr : 0 < r) :
    scaledBoxCrossMin ξ g c ρ r =
      ENNReal.ofReal r * boxCrossMin ξ (fun x => g ((r : ℂ) * x)) c ρ := by
  simp only [scaledBoxCrossMin, boxCrossMin,
    crossLenIn_image_mul ξ g _ _ _ hr, mul_min]

end SupercriticalLQGUniqueness.B2.DG20Pt
