/-
# Translation invariance of the Fourier-side Sobolev norm

`‖f(· + h)‖_{H^s} = ‖f‖_{H^s}`: the Fourier translation identity
`fourier_comp_add_right_lift` writes
`𝓕 (f(·+h)) ξ = 𝐞 ⟪h,ξ⟫ • 𝓕 f ξ`; the character acts by
an isometry of `ℂ`.  This is the input of the mollification step in the
classical Fréchet–Kolmogorov proof of `FrechetKolmogorovH`
(`FrechetKolmogorov.lean`): the convolution remainder
`ρ_ε * f − f = ∫ ρ_ε(y) (f(·−y) − f) dy` is bounded in `H^s` by the
supremum of the translated differences.
-/
import LatticeProb.Analysis.Sobolev.TranslationBound

open MeasureTheory
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

/-- **Translation invariance of `sobolevNormSq`.** -/
theorem sobolevNormSq_comp_add_right {d : ℕ} (s : ℝ) (f : Space d → ℝ) (h : Space d) :
    sobolevNormSq d s (fun x => f (x + h)) = sobolevNormSq d s f := by
  unfold sobolevNormSq
  refine lintegral_congr fun ξ => ?_
  have hF : (fun x : Space d => ((f (x + h) : ℝ) : ℂ))
      = (fun x : Space d => (fun y : Space d => (f y : ℂ)) (x + h)) := rfl
  have h1 : 𝓕 (fun x : Space d => ((f (x + h) : ℝ) : ℂ)) ξ
      = 𝐞 (inner ℝ h ξ) • 𝓕 (fun x : Space d => (f x : ℂ)) ξ := by
    rw [hF]
    exact congrFun (fourier_comp_add_right_lift (fun y : Space d => (f y : ℂ)) h) ξ
  have hnorm : ‖𝐞 (inner ℝ h ξ) • 𝓕 (fun x : Space d => (f x : ℂ)) ξ‖
      = ‖𝓕 (fun x : Space d => (f x : ℂ)) ξ‖ := by
    exact Circle.norm_smul _ _
  rw [h1, hnorm]

end LatticeProb.Sobolev
