/-
# The high-frequency phase bound for the translation estimate

The companion `TranslationBound.lean` controls `𝐞 ⟪h,ξ⟫ − 1` at bounded frequency
(`norm_fourierChar_sub_one_le`): `‖𝐞 t − 1‖ ≤ 4π|t|` for `2π|t| ≤ 1`.  Beyond the cutoff the
trivial bound `‖𝐞 t − 1‖ ≤ 2` is used; this module lands it, the second half of the phase
estimate in the quantitative translation bound for the Fréchet–Kolmogorov route.
-/
import LatticeProb.Analysis.Sobolev.TranslationBound

open scoped FourierTransform

namespace LatticeProb.Sobolev

/-- **The phase difference is at most `2`.** -/
theorem norm_fourierChar_sub_one_le_two (t : ℝ) :
    ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ 2 := by
  calc ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ ‖((𝐞 t : Circle) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Circle.norm_coe, norm_one]; norm_num

end LatticeProb.Sobolev
