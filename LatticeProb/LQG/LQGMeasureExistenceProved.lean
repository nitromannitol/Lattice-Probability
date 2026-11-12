import LatticeProb.LQG.GMCOriginGrowth
import LatticeProb.LQG.LQGMeasureOriginBound

/-!
# Existence of the LQG measure of the whole-plane Gaussian free field

For `0 < γ < 2` and `α₀ < Q = 2/γ + γ/2`, the LQG measure of the whole-plane Gaussian free field with an
`α₀`-log singularity at the origin, `e^{γ (h - α₀ log|·|)} d²z`, exists as the almost sure vague limit of the
circle-average approximations along the dyadic scales (Duplantier-Sheffield; Berestycki-Powell, Theorem 2.1 and
Section 2.5 for the singular weight).

The proof combines
* the reduction to an almost sure bound of the mass near the origin
  (`LQGMeasureOriginBound.lqgMeasureExistenceLP_of_eventually_le`), and
* the subexponential growth of `e^{γ h_{2^{-j}}(0)} Z_j`, where `Z_j` is the maximal unit-ball mass of the dilated
  recentred field at scale `2^{-j}` (`IsWholePlaneGFF.ae_eventually_exp_circle_mul_maximal_dilated_le`).

## Main statement

* `lqgMeasureExistenceLP_proved`: `LQGMeasureExistenceLP P γ α₀ hC hcirc` holds for every `γ`, `α₀`.
-/

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- **Existence of the LQG measure with an `α₀`-log singularity.** For every whole-plane Gaussian free field,
every `0 < γ < 2` and every `α₀ < Q`, the circle-average approximations of `e^{γ (h - α₀ log|·|)} d²z` converge
vaguely along the dyadic scales, almost surely. -/
theorem lqgMeasureExistenceLP_proved {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureExistenceLP P γ α₀ hC hcirc :=
  LQGMeasureOriginBound.lqgMeasureExistenceLP_of_eventually_le P hC hcirc fun hG hγ hγ2 =>
    hG.ae_eventually_exp_circle_mul_maximal_dilated_le hγ hγ2

end LatticeProb.LQG
